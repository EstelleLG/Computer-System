/*
 * mm.c Use an explicit list with LIFO order to create a dynamic memory
 *
 *
 *
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "gcompiler",
    /* First member's full name */
    "Xinyi Gong",
    /* First member's WUSTL key */
    "gongxinyi",
    /* Second member's full name (leave blank if none) */
    "Yuan Gao",
    /* Second member's WUSTL key (leave blank if none) */         /******* changed this *********/
    "gao.yuan"
};


//basic constants and macros from book page 857
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define INITSIZE   (1<<8)   /* Initialize heap  */


#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  	(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
//line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and prev blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))      //bp+ blocksize = nextbp



/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8


/* rounds up to the nearest multiple of ALIGNMENT */

//rounds up!!!!!!!! by clearing the last three bits.
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


#define MIN_BLOCK_SIZE 16         //4 words header + footer + pred + succ
#define INIT_LIST_SIZE 24         //padding+prologue header+prologue footer + prologue pointer*2 + epilogue header
#define PADDING        1<<7       //adjusted newsize in mmrealloc

//get the pointer that points to the next free block, stored in bp / or bp+DSIZE.
#define NEXT_FREE(bp)   (*(void **)(bp + WSIZE))
#define PREV_FREE(bp)   (*(void **)(bp))


static void* heap_listp;
static void* free_listp;

static void LIFO_add(void *bp);
static void LIFO_delete(void *bp);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);


/* Heap consistency checker */
#define FREE_LIST_CHECK      -1
#define CONTIGUOUS_CHECK     -2
#define FREE_BLOCK_CHECK     -3
#define OVERLAP_BLOCK_CHECK  -4

int in_free_list(void *ptr);
int mm_check(void);




/**
 * LIFO_add
 * Implement add using LIFO to add a block to the free list
 **/
static void LIFO_add(void *bp) {
    
    //overwrite bp's two pointers
    NEXT_FREE(bp) = free_listp;  //free_listp is the old starting point.
    PREV_FREE(free_listp) = bp;
    PREV_FREE(bp) = NULL;  //first block
    
    //update free_listp;
    free_listp = bp;
}


/*
 * LIFO_delete - Implement delete function by LIFO
 * delete the block from free list after allocate a free block, or coalesced.
 */
static void LIFO_delete(void *bp) {
    
    if (PREV_FREE(bp) == NULL) {
        //update the first block
        free_listp = NEXT_FREE(bp);
        PREV_FREE(NEXT_FREE(bp)) = NULL;
    }
    else if (NEXT_FREE(bp) == NULL) {
        NEXT_FREE(PREV_FREE(bp)) = NULL;
    }
    
    else {
        NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
        PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
    }
    
}


/*
 * coalesce - To coaloesce the free block with any free block before/after it
 * Four different cases
 */
static void *coalesce(void *bp) {
    
    size_t previous_alloc = GET_ALLOC((char *)bp - DSIZE);
    
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    
    //old size
    size_t size = GET_SIZE(HDRP(bp));
    
    //case 1. Both are allocated
    if (previous_alloc && next_alloc) {
        
        //implement LIFO. add this free block to the first block of list.
        LIFO_add(bp);
    }
    
    //case 2. Next is free.
    if (previous_alloc && !next_alloc) {
        //n+m2
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        //delete the second block from the free list
        LIFO_delete(NEXT_BLKP(bp));
        
        PUT(HDRP(bp), PACK(size, 0));
        
        //after updating bp's size, we can just find footer of bp instead of bp's next.
        PUT(FTRP(bp), PACK(size, 0));
        //add new block
        LIFO_add(bp);
    }
    
    //case 3. Previous block is free.
    else if (!previous_alloc && next_alloc) {
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        
        bp = PREV_BLKP(bp);
        //remove previous block
        LIFO_delete(bp);
        
        //update size
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
        LIFO_add(bp);
    }
    
    //case 4. Both are free.
    else if (!previous_alloc && !next_alloc) {
        //n+m1+m2
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        //delete prev and next;
        LIFO_delete(PREV_BLKP(bp));
        LIFO_delete(NEXT_BLKP(bp));
        
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
        LIFO_add(bp);
    }
    
    return bp;
    
    
}



/*
 * Extend heap using mem_sbrk, when the current heap is not sufficient to hold the data
 * Refer to textbook page 858
 */
static void *extend_heap(size_t words) {
    
    void *bp;
    size_t size;
    
    //allocate an even number of words
    size = (words % 2 ) ? (words+1) * WSIZE : words * WSIZE;
    
    //for explicit free list, MIN_BLOCK_SIZE may > size after alignment
    if (size < MIN_BLOCK_SIZE) {
        size = MIN_BLOCK_SIZE;
    }
    
    
    if ((long)(bp = mem_sbrk(size)) == -1 ) {
        return NULL;
    }
    
    //update the new heap
    PUT(HDRP(bp), PACK(size, 0));   //new block header
    PUT(FTRP(bp),  PACK(size, 0));  //new block footer
    
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   //new epilogue header
    
    return coalesce(bp);  // possible coalesce
    
}



/*
 * mm_init - initialize the malloc package.
 * Refer to textbook page 858
 */
int mm_init(void)
{
    //heap_listp points to the starting padding.
    
    //allocate initial list size
    if ((heap_listp = mem_sbrk(INIT_LIST_SIZE)) == NULL) {
        return -1;
    }
    
    //aligment padding
    PUT(heap_listp, 0);
    
    //prologue block header
    PUT(heap_listp + WSIZE, PACK(MIN_BLOCK_SIZE, 1));
    
    //prologue pred pointer
    PUT(heap_listp + 2*WSIZE, 0);
    PUT(heap_listp + 3*WSIZE, 0); //succ pointer
    
    //prologue block footer
    PUT(heap_listp + MIN_BLOCK_SIZE, PACK(MIN_BLOCK_SIZE, 1));
    
    //epilogue block header
    PUT(heap_listp + WSIZE + MIN_BLOCK_SIZE, PACK(0, 1));
    
    //free_listp points to the initial position
    free_listp = heap_listp + DSIZE;
    
    
    //extend the empty head
    if (extend_heap((INITSIZE) / WSIZE) == NULL) {
        return -1;
    }
    
    return 0;
    
    
}


/*
 * find_fit - to find a suitable free block that can hold size asize
 * Refer to the textbook
 */
static void *find_fit(size_t asize) {
    
    //search the free list
    //check if bp is free, and it has larger size than requested asize.
    
    void *bp = free_listp;
    
    while (bp != NULL) {
        if (GET_ALLOC(HDRP(bp)) == 0) { //if free
            if (GET_SIZE(HDRP(bp)) >= asize) {  //if there is enough space
                //we find a sufficiently large free block
                
                return bp;
            }
        }
        
        bp = NEXT_FREE(bp);
        
    }
    
    //fail to break from while = fail to find such bp;
    return NULL;
    
}

/*
 * place - place size into the block pointed by bp
 * If the block has more space than needed, split it and free the second half
 */
static void place(void * bp, size_t size) {
    
    //size of free block found
    size_t free_size = GET_SIZE(HDRP(bp));
    int rest_size = free_size - size;
    
    //if the unused free space can hold another minimal block, split bp block.
    if (rest_size >= MIN_BLOCK_SIZE) {
        
        //update allocated bit
        //part of the free bp
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        
        //remove bp from the free list
        LIFO_delete(bp);
        
        
        //rest part of the bp that can be used later
        void* restbp = NEXT_BLKP(bp);
        PUT(HDRP(restbp), PACK(rest_size, 0));
        PUT(FTRP(restbp), PACK(rest_size, 0));
        //add restbp to the free list
        coalesce(restbp);
    }
    
    else {
        
        //update allocate bit
        //padding in the payload
        PUT(HDRP(bp), PACK(free_size, 1));
        PUT(FTRP(bp), PACK(free_size, 1));
        
        //remove bp from the free list
        LIFO_delete(bp);
    }
    
}


/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 * Refer to textbook page 861
 */
void *mm_malloc(size_t size) {
    
    
    size_t asize;
    size_t extendedsize;
    void *bp;
    
    if (size == 0) {
        return NULL;
    }
    
    //for an allocated block, we need at least 8 bytes, so +payload+alignment = at least 16 bytes
    //ALIGN(size) + footer+header
    asize = MAX(ALIGN(size) + DSIZE, MIN_BLOCK_SIZE);
    
    //if we can find a place.
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    
    //no fit found
    extendedsize = MAX(asize, CHUNKSIZE);
    
    if ((bp = extend_heap(extendedsize / WSIZE)) == NULL) {
        return NULL;
    }
    
    place(bp, asize);
    
    return bp;
    
}

/*
 * mm_free - Freeing a block does nothing.
 * Refer to textbook page 860
 */
void mm_free(void *ptr) {
    
    if (ptr == NULL) {
        return;    //return nothing
    }
    
    //check if ptr block is allocated
    if (GET_ALLOC(HDRP(ptr)) == 0) {
        return;
    }
    
    size_t size = GET_SIZE(HDRP(ptr));
    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    coalesce(ptr);
    
}



/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    
    //if size is 0
    if (size == 0) {
        mm_free(ptr);
        return ptr;
    }
    
    size_t old_size = GET_SIZE(HDRP(ptr));
    //align the size required
    size_t new_size = MAX(ALIGN(size + DSIZE), MIN_BLOCK_SIZE);
    new_size += PADDING;
    
    void * bp;
    
    // check whether current block is sufficient to hold the new block
    if (old_size >= new_size) {
        //allocate the smaller block and free the old bigger block
        bp = mm_malloc(new_size);
        memcpy(bp, ptr, size);
        mm_free(ptr);
        
        return bp;
    }
    
    else { //old_size < new_size
        int diff = new_size - old_size;
        
        //if ptr is at the bottom of the current heap (epilogue)
        size_t next_block_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        if (next_block_size == 0) { //epilogue block header
            
            //extend heap by diff
            void * extended_bp = extend_heap(diff / WSIZE);
            
            if (extended_bp == NULL) { //cannot allocate more heap
                return ptr;
            }
            //combine two blocks
            PUT(HDRP(ptr), PACK(new_size, 1));
            PUT(FTRP(ptr), PACK(new_size, 1));
            
            return ptr;
        }
        
        //use find_fit to find an altenative free block to hold it
        if ((bp = find_fit(new_size)) != NULL) {
            place(bp, new_size);
            memcpy(bp, ptr, old_size);
            mm_free(ptr);
            return bp;
        }
        
        // if there's no free block large enough to hold, extend heap
        else {
            
            bp = extend_heap(new_size / WSIZE);
            
            //run out of heap
            if (bp == NULL) {
                return ptr;
            }
            
            place(bp, new_size);
            memcpy(bp, ptr, GET_SIZE(HDRP(ptr)));
            //PUT(HDRP(bp), PACK(new_size, 1));
            //PUT(FTRP(bp), PACK(new_size, 1));
            mm_free(ptr);
            
            return bp;
            
        }
        
        
    }
    
    

}


/*
 *in_free_list - Check whether block ptr in heap list is in free list
 */
int in_free_list(void *ptr) {
   
    void *bp;
    for (bp = free_listp; bp != NULL; bp = NEXT_FREE(bp)) {
        if (bp == ptr) {
            return 0;
        }
    }
    
    return -1;
    
    
}

/*
 *mm_check - check heap consistency
 */
int mm_check(void) {
    void *bp;
    
    //check if every block in the free list is marked as free.
    for (bp = NEXT_FREE(free_listp); bp != NULL; bp = NEXT_FREE(bp)) {
        if (GET_ALLOC(HDRP(bp)) == 1) {
            return FREE_LIST_CHECK;
        }
        
    }
    
    //check if there are any contiguous free blocks.
    void *nextbp;
    for (bp = free_listp; NEXT_FREE(bp) != NULL; bp = NEXT_FREE(bp)) {
        nextbp = NEXT_BLKP(bp);
        if (NEXT_FREE(bp) == nextbp) {  //contiguous
            return CONTIGUOUS_CHECK;
        }
        
    }
    
    //check if every free block is actually in the free list;
    void *startbp; // 6 = padding(1)+prologue(4)+header of the first block(1)
    for (startbp = heap_listp + 6*WSIZE; GET_SIZE(HDRP(startbp)) != 0;
         startbp = NEXT_BLKP(startbp)) {
        
        if (GET_ALLOC(HDRP(startbp)) == 0) { //free block
            if (in_free_list(startbp) != 0) {
                return FREE_BLOCK_CHECK;
            }
        }
        
        //check if allocated blocks are overlap
        else { //allocated block
            if (NEXT_BLKP(startbp) != NULL) {
                if ((GET_SIZE(HDRP(startbp)) + startbp) != NEXT_BLKP(startbp)) {
                    return OVERLAP_BLOCK_CHECK;
                }
            }

        }
        
    }
    

    return 0;
}







