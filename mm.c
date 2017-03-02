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
 * User 1: gunnlaugur15
 * SSN: 1707952889
 * User 2: hjalmarh15
 * SSN: 1510933379
 * User 3: fridrik14
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
    "Fridrik Thor Hjalmarsson",
    /* Third member's email address (leave blank if none) */
    "Fridrik14@ru.is"
};
/* $begin mallocmacros */
/* Basic constants and macros */

#define WSIZE       4        /* word size (bytes) */
#define DSIZE       8        /* doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12) /* initial heap size (bytes) */
#define OVERHEAD    8        /* overhead of header and footer (bytes) */


/* #define MAX(x, y) ((x) > (y) ? (x) : (y)) */
inline MAX(int x, int y){
	return ((x) > (y) ? (x) : (y));
}

/* Pack a size and allocated bit into a word */
/* #define PACK(size, alloc)  ((size) | (alloc)) */
inline PACK(size_t size, size_t alloc){
	return ((size) | (alloc));
}

/* Read and write a word at address p. */
/* #define GET(p)       (*(size_t*)(p)) */
/* #define PUT(p, val)  (*(size_t *)(p) = (val)) */
inline GET(char *p){
	return (*(size_t*)(p));
}
inline PUT(char *p, size_t val){
	return (*(size_t *)(p) = (val));
}

/* Read the size and allocated fields from address p */
/* #define GET_SIZE(p)   (GET(p) & ~0x7) */
/* #define GET_ALLOC(p)  (GET(p) & 0x1) */

inline GET_ALLOC(char *p){
	return (GET(p) & 0x1);
}

inline GET_SIZE(char *p){
	return (GET(p) & ~0x7);
}

/* Given block ptr bp, compute address of its header and footer */
/*#define HDRP(bp)  ((char *)(bp) - WSIZE) */
/*#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) */
inline HDRP(char *bp){
	return ((char *)(bp) - WSIZE);
}

inline FTRP(char *bp){
	return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}
/* Given block ptr bp, compute address of next and previous blocks */
/* #define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) */
/* #define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) */

inline NEXT_BLKP(char *bp){
	return ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
}

inline PREV_BLKP(char *bp){
	return ((char *)(bp) - GET_SIZE(((char *)(bp) - WSIZE)));
}
/* Given free ptr bp, compute address of next and previous blocks
 * in the free list */
/*#define NEXT_FREE(bp)  (*(char **)(bp + WSIZE)) */
/*#define PREV_FREE(bp)  (*(char **)(bp)) */

inline NEXT_FREE(char *bp){
	return (*(char **)(bp + WSIZE));
}

inline PREV_FREE(char *bp){
	return (*(char **)(bp));
}

/* Global declarations */
static char *heap_listp = 0; /* pointer to the first block */
static char *free_listp = 0; /*pointer to the beginning of our free list */

/* Function prototypes for internal helper routines */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void checkblock(void *bp);
static void printblock(void *bp); 
int mm_check();
static void insert_into_free_list(void *bp);
static void remove_from_free_list(void *bp);
static size_t adjust_and_align(size_t size);
/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {
  
    /* Create the initial empty heap. */
    if ((heap_listp = mem_sbrk(8*WSIZE)) == NULL) 
        return -1;

    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp +  WSIZE,  PACK(OVERHEAD, 1));  /* Prologue header */ 
    PUT(heap_listp + DSIZE, PACK(OVERHEAD, 1));    /* Prologue footer */ 
    PUT(heap_listp + DSIZE+WSIZE, PACK(0, 1));     /* Epilogue header */
  
    /* initialize our free list pointer */
    free_listp = heap_listp + DSIZE; 

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(4) == NULL){ 
        return -1;
    }
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmalloc */
void *mm_malloc(size_t size) 
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *bp;

    /* Ignore spurious requests. */
    if (size == 0)
    return (NULL);

    /* Adjust block size to include overhead and alignment reqs. */
    asize = adjust_and_align(size);

    /* Search the free list for a fit. */
    if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return (bp);
    }

    /* No fit found.  Get more memory and place the block. */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
    return (NULL);
    place(bp, asize);
    return (bp);
} 
/* $end mmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *bp){
    size_t size =  GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - naive implementation of mm_realloc 
 */
void *mm_realloc(void *ptr, size_t size){
    void *newp;
    size_t copySize, asize, nextSize, extendSize;
    asize = adjust_and_align(size);

    /* if ptr is NULL it is the same as calling mm_malloc(size) */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    /* if size is 0 it is the same as calling mm_free(ptr) */
    else if(size == 0) {
        mm_free(ptr);
        return 0;
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (asize <= copySize) {
        return ptr;
    }
    

    /* Special Cases -
        next block is free and big enough
        next block is free but not big enough but is at the end
        our ptr block is the last block
    */

   
    nextSize = GET_SIZE(HDRP(NEXT_BLKP(ptr))); //size of the next block
    
    /*Case 1 -  check if next block is free and big enough */
    if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) && nextSize + copySize >= asize) {
        remove_from_free_list(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(nextSize+copySize, 1));
        PUT(FTRP(ptr), PACK(nextSize+copySize, 1));
        return ptr;
    }
    /*Case 2 - check if next block is free and the last block */
    else if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) && GET_SIZE(HDRP(NEXT_BLKP(NEXT_BLKP(ptr))))  == 0) {
        extendSize = MAX(asize - (copySize + nextSize), CHUNKSIZE);
        newp = extend_heap(extendSize/WSIZE);
        remove_from_free_list(NEXT_BLKP(ptr));
        nextSize = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(nextSize+copySize,1));
        PUT(FTRP(ptr), PACK(nextSize+copySize,1));
        return ptr;
    }
    /* Case 3 - check if current block is at the end */
    else if(nextSize == 0) {
        extendSize = MAX(asize - copySize, CHUNKSIZE);
        newp = extend_heap(extendSize/WSIZE);
        remove_from_free_list(NEXT_BLKP(ptr));
        nextSize = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(nextSize+copySize,1));
        PUT(FTRP(ptr), PACK(nextSize+copySize,1));    
        return ptr;
    }
    /* if nothing above works, we just malloc a new block and return it */
    if((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }

    copySize = GET_SIZE(HDRP(ptr));
    if(size < copySize) {
        copySize = size;
    }

    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
    
}

/*
 * Checks the heap for consistency. Returns a nonzero value if and only if
 * the heap is consistent.
 * Checks if
 *     The prologue/epilogue headers are right
 *     The headers match the footers
 *     Every block in the free list is marked as free
 *     Adjacent free blocks should have been coalesced
 *     Every free block is actually in the free list
 */
int mm_check(void) {
    char *bp;
    int is_good = 1;
    /*
     *Checks the prologue header. If it is not of size 8 or is not allocated
     *it is not right
    */
    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
        printf("Bad prologue header\n");
        is_good = 0;
    }

    /*
     *runs through every block on the heap and checks if
     *   we are doubleword aligning
     *   a free block is in our free list
     *   there are adjacent free blocks that need to be coalesced
     *   
    */

    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if((size_t)bp % 8) {
            printf("Error: %p is not doubleword aligned\n", bp);
            is_good = 0;
        }
        /* if we find a free block, we traverse the free list to see if it is in the list */
        if(!GET_ALLOC(HDRP(bp))){
            char* temp_ptr;
            int found = 0;
            for(temp_ptr = free_listp; GET_ALLOC(HDRP(temp_ptr)) == 0; temp_ptr = NEXT_FREE(temp_ptr)){
                if(temp_ptr == bp){
                    found = 1;                                                                                                      break;
                }
            }
            if(!found) {
                printf("Block %p is not in the free list", bp);
                is_good = 0;
            }
        }
    }

    /*
     *Checks the epilogue header. If it is not of size 0 and not allocated
     *it is not right
     */
     if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
         printf("Bad epilogue header\n");
         is_good = 0;
     }


     /*
      *     Check if every block in our free list is actually free.
      *
      */

     for(bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREE(bp)){
        if(GET_ALLOC(bp)){
            printf("Block %p in free list is actually not free", bp);    
            is_good = 0;
         }
     }

     return is_good;

}


/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((int)(bp = mem_sbrk(size)) == -1){ 
    return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    return coalesce(bp);
}
/* $end mmextendheap */


/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize){
    /* First fit search - traverse our free list and
    * choose the first block that is big enough */

    void *bp;
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREE(bp) ){
        if (asize <= (size_t)GET_SIZE(HDRP(bp)) ) {
            return bp;
        }
    }
    return NULL;
}


/*
 * place - Place block of asize bytes at start of free block bp
 *          and split if remainder would be at least minimum block size
 */

/* $begin mmplace */
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (DSIZE+OVERHEAD)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_from_free_list(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_from_free_list(bp);
    }
}
/* $end mmplace */


/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp){

    /* checks if next block is allocated*/
    size_t NEXT_ALLOC = GET_ALLOC(  HDRP(NEXT_BLKP(bp))  );

    /* checks if previous block is allocated or if we are at the front of the heap */
    size_t PREV_ALLOC = GET_ALLOC(  FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp ;
    size_t size = GET_SIZE(HDRP(bp));
  
    /* Case 1 - only the next block is free
    *            here we remove the next block from the free list
    *            and make a new block with the combined size of
    *            current block and next block
    */
    if (PREV_ALLOC && !NEXT_ALLOC) {                  
        size += GET_SIZE( HDRP(NEXT_BLKP(bp))  );
        remove_from_free_list(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Case 2 - only the prevous block is free
    *        here we remove from the free list
    *        and make a new block with combined size of
    *        current block and previous block
    */  
    else if (!PREV_ALLOC && NEXT_ALLOC) {               
        size += GET_SIZE( HDRP(PREV_BLKP(bp))  );
        bp = PREV_BLKP(bp);
        remove_from_free_list(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Case 3 - both next and previous blocks are free
    *        here we remove both next and previous blocks
    *        from the free list and make a new block with a combined
    *        size of previous, current and next blocks
    */ 
    else if (!PREV_ALLOC && !NEXT_ALLOC) {                
        size += GET_SIZE( HDRP(PREV_BLKP(bp))  ) + GET_SIZE( HDRP(NEXT_BLKP(bp))  );
        remove_from_free_list(PREV_BLKP(bp));
        remove_from_free_list(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /*insert the new block into the free list */
    insert_into_free_list(bp);
    return bp;
}

/*insert a block into the free list*/
static void insert_into_free_list(void *bp)
{
    if(bp == NULL) {
        return;
    }
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
/*remove block from the free listt*/
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


static void printblock(void *bp) {
    size_t hsize, halloc, fsize, falloc;


    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: end of heap\n", bp);
        return;
    }

    printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
      hsize, (halloc ? 'a' : 'f'), 
      fsize, (falloc ? 'a' : 'f'));
}


static void checkblock(void *bp) {

    if ((int)bp % DSIZE)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

static size_t adjust_and_align(size_t size) {
    size_t asize;
    if (size <= DSIZE)
        asize =  DSIZE + OVERHEAD;
    else
        asize = DSIZE * ((size + OVERHEAD + (DSIZE - 1)) / DSIZE);

    return asize;
}
