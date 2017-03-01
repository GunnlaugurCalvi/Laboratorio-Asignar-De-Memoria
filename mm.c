/* 
 * mm.c 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * We will be using explicit free list with first fit implementation.
 * Each free block has a header and a footer which contain size/allocation
 * information about the block(see above). The block also has a next and prev
 * pointer that points to the next and previous free blocks in the list.
 * 
 * A free block looks like this:
 *  ------------------------------------------------------------------------------------
 * | header - size/allocated | prev | next | free space ..... | footer - size/allocated |
 *  ------------------------------------------------------------------------------------
 *
 * An allocated block looks like this:
 *  ----------------------------------------------------------------------
 * | header -size/allocated | payload + padding | footer - size/allocated |
 *  ----------------------------------------------------------------------
 *
 *
 *
 * The heap looks like this:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(0:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 * 
 */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in below _AND_ in the
 * struct that follows.
 *
 * Note: This comment is parsed. Please do not change the
 *       Format!
 *
 * === User information ===
 * Group: Tres Hombres Cinco Cojones
 * User 1: Gunnlaugur15
 * SSN: 1707952889
 * User 2: Hjalmarh15
 * SSN: 1510933379
 * User 3: Fridrik14
 * SSN: 2911942659
 *  === End User Information ===
 *******************************************************/
team_t team = {
    /* Group name */
    "Tres Hombres Cinco Cojones",
    /* First member's full name */
    "Gunnlaugur Kristinn Hreidarsson Calvi",
    /* First member's email address */
    "gunnlaugur15@ru.is",
    /* Second member's full name (leave blank if none) */
    "Hjalmar Orn Hannesson",
    /* Second member's email address (leave blank if none) */
    "hjalmarh15@ru.is",
    /* Third full name (leave blank if none) */
    "Fridirik Thor Hjalmarsson",
    /* Third member's email address (leave blank if none) */
    "Fridrik14@ru.is"
};

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)         (*(size_t *)(p))
#define PUT(p, val)    (*(size_t *)(p) = (val))  

/* (which is about 49/100).* Read the size and allocatfed fields from address p */
#define GET_SIZE(p)    (GET(p) & ~0x7)
#define GET_ALLOC(p)   (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of next and previous free blocks */
#define NEXT_FREE(bp) (*(char**)(bp+WSIZE))
#define PREV_FREE(bp) (*(char**)(bp))


/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */  
static char *free_listp;  /* pointer to the beginning of our free list */

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);
static void insert_into_free_list(void *bp);
static void remove_from_free_list(void *bp);

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL) {
        return -1;
    }
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */

    /* make start of free list point to prologue footer */
    free_listp = heap_listp + DSIZE;
    heap_listp = heap_listp + DSIZE;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0) {
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {
        asize = DSIZE + OVERHEAD;
    }
    else {
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    }
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp; 
    
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize) {
        copySize = size;
    }
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/*
Checks the heap for consistency. Returns a nonzero value if and only if
the heap is consistent. 
Checks if
    The prologue/epilogue headers are right
    The headers match the footers
    
    Every block in the free list is marked as free
    Adjacent free blocks should have been coalesced
    Every free block is actually in the free list
*/
int mm_check(void){
	
    char *bp;
    /*
    Checks the prologue header. If it is not of size 8 or is not allocated
    it is not right
    */
	if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
		printf("Bad prologue header\n");
	}
	

    /* 
    runs through every block on the heap and checks if
        we are doubleword aligning
        header matches the footer
        a free block is in our free list
        there are adjacent free blocks that need to be coalesced
     */
	for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if ((size_t)bp % 8) {
        	printf("Error: %p is not doubleword aligned\n", bp);
    	}
		if (GET(HDRP(bp)) != GET(FTRP(bp))) {
			printf("Error: header does not match footer\n");
		}

        if(!GET_ALLOC(bp)) {
            //TODO Check if the free block is in our free list.
            continue;
        }

        //Checks if there are free blocks adjacent that need to be coalesced
        if(!GET_ALLOC(bp) && !GET_ALLOC(NEXT_BLKP(bp))) {
            printf("Two free blocks in a row, should be coalesced");
        }

	}

    /*
    Checks the epilogue header. If it is not of size 0 and not allocated
    it is not right.
    */
	if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("Bad epilogue header\n");
    }


    /*
    Check if every block in our free list is actually free.
    */

    /*
    TODO loop through our free list. Inside the loop:
        if(GET_ALLOC(curr)) {
            printf("block in free list not actually free");
        }

    */
    return 1;
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
        
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));   

    /* TODO
        remove block from free list.
    */
    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
        //if we split we need to remove from free list and then add new block to free list
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else { 
        //if we don't we just remove from the free list
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{   

    /* TODO
        change this so we traverse free list instead of all the heap
    */

    /* first fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));


    /* TODO
        remove blocks to be coalesced from free list
        insert newly coalesced block into the free list

    */
    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        printf("test");
        //remove next block from free list?
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        //remove prev block from free list
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {                                     /* Case 4 */

        //remove next and prev blocks from free list
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }


    //insert new bp into the free list
    return bp;
}

static void insert_into_free_list(void *bp)
{
    /* when we insert a free block into the free list we insert
     * it at the front of the list and
            make the new front->next point to old front
            make old front->prev point to new front
            make the new front->prev point to NULL
            make the start of the free list point to new front */

    NEXT_FREE(bp) = free_listp;
    PREV_FREE(free_listp) = bp;
    PREV_FREE(bp) = NULL;
    free_listp = bp;
}

static void remove_from_free_list(void *bp)
{
    /* when removing from the list we have two cases:
     *  1) we are removing from the front of the list
            in this case we make the start of the list skip
            the block thats about to be removed and point to
            the next block in the list
     *  2) we're not removing from the front of the list
            in this case we "cross the wires" so to speak and
            skip over the block that's about to be deleted.
            If we have a prev, curr and next pointer we make
            prev point to next and next point to prev so we skip
            over our curr pointer.
    */
    
    //case 1
    if(!PREV_FREE(bp)) {
        free_listp = NEXT_FREE(bp);
    }
    //case 2
    else {
        NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
    }
    PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
}
static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8) {
        printf("Error: %p is not doubleword aligned\n", bp);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("Error: header does not match footer\n");
    }
}
