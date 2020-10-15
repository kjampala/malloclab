/*
 * My approach involves using segregated free lists which provides
 * an arry of free lists that I can use. Each array contains blocks
 * of the same size (2^n to 2^(n+1)-1). I'll have a global pointer
 * which points to the first element in the array. The segregated list
 * is size = count * wsize and each entry point will hold the location
 * of the first block. Blocks are inserted/removed when the segregated
 * lists are freed or malloc'd. All blocks will have a header and footer
 * and will contain size and allocation bit. Block allocation will be
 * determined by finding the best fit and will be optimized for binary 
 * sizes.
 */
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//Basic constants and macros
#define WSIZE 4         //word and header/footer size (bytes)
#define DSIZE 8         //double word size
#define CHUNKSIZE (1<<12)           //extend heap by this amount (bytes)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

//pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

//read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

//read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

//given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//global variables
static char *heap_listp = 0;        //first block pointer
static char *rover;             //next block pointer
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

// Header Node. Contains a single field which is the packed size 
// and is allocated
typedef struct header {
    size_t size_alloc;
} header_t;

// Footer Node. Contains a single field which is the packed size 
// and is allocated
typedef struct footer {
    size_t size_alloc;
} footer_t;

// FreeBlock Node. Contained within unallocated blocks. Can be used to implement
// an explicit free list.
typedef struct freeblock {
    struct freeblock *next;
    struct freeblock *prev;
} freeblock_t;

void put_footer(footer_t *f, size_t size, bool alloc) {
    assert(f);
    assert(size % ALIGNMENT == 0);
    f->size_alloc = (alloc & 0x1) | size;
}

size_t get_size_footer(footer_t *f) {
    assert(f);
    return (~0x7) & f->size_alloc;
}

void put_header(header_t *h, size_t size, bool alloc) {
    assert(h);
    assert(size % ALIGNMENT == 0);
    h->size_alloc = alloc | size;
}

size_t get_size(header_t *h) {
    assert(h);
    return (~0x7) & h->size_alloc;
}

size_t get_alloc(header_t *h) {
    assert(h);
    return h->size_alloc & 0x1;
}

footer_t *get_footer(header_t *h) {
    assert(h);
    return (footer_t *)(((size_t)h) + get_size(h) - sizeof(footer_t));
}

header_t *get_header(void *p) {
    assert(p);
    return (header_t *)(((size_t)p) - sizeof(header_t));
}

header_t *get_above_header(header_t *h) {
    assert(h);
    return (header_t *)(((size_t)h) + get_size(h));
}

header_t *get_below_header(header_t *h) {
    assert(h);
    footer_t *prev_footer = (footer_t *)(((size_t)h) - sizeof(footer_t));
    return (header_t *)(((size_t)h) - get_size_footer(prev_footer));
}

void *get_payload(header_t *h) {
    assert(h);
    return (void*)(((size_t) h) + sizeof(header_t));
}

freeblock_t *get_freeblock(header_t *h) {
    assert(h);
    return (freeblock_t *)(((size_t)h) + sizeof(header_t));
}

header_t *get_freeblock_header(freeblock_t *freeblock) {
    assert(freeblock);
    return (header_t *)(((size_t)freeblock) - sizeof(header_t));
}

/* 
 * mm_init - initialize the malloc package.
 * creates empty free list, creates initial free block through heap extension
 */
int mm_init(void) {
    //code is based off of Computer Systems Textbook, Section 9.9
    //Dynamic Memory Allocation page 894, figure 9.44

    //create the intial empty heap
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    rover = heap_listp;

    //extend the empty heap with a free block of CHUNKSIZE bytes
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    //code is based off of Computer Systems Textbook, Section 9.9
    //Dynamic Memory Allocation page 897, figure 9.47
    size_t asize;       //adjusted block size
    size_t extendsize;      //amount to extend heap if no fit
    char *bp;

    //ignore fake requests
    if(size == 0) {
        return NULL;
    }

    //adjust block size to include overhead and alignment reqs
    if(size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    //search the free list for a fit
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    //no fit found get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 * The most recently allocated block is freed and then
 * the adjacent blocks are merged.
 */
void mm_free(void *bp) {
    //code is based off of Computer Systems Textbook, Section 9.9
    //Dynamic Memory Allocation page 896, figure 9.46
    if(bp == 0) {
        return;
    }
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * Following the limits addressed in the handout, the pointer to the
 * allocated region of a certain size bytes is returned.
 */
void *mm_realloc(void *oldptr, size_t size) {
    // Basic Implementation with elements from Computer Systems Textbook and Assignment Handout
    void *old = oldptr;
    void *newptr;
    size_t copy;
    
    //gets a new pointer block
    newptr = mm_malloc(size);
    if (newptr == NULL){
      return NULL;
    }

    //call the free method if the size is 0
    if(size == 0){
        mm_free(oldptr);
        return 0;
    }

    //copy over the old data
    copy = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copy){
      copy = size;
    }

    memcpy(newptr, oldptr, copy);
    mm_free(oldptr);
    return newptr;
}

/*
 * mm_check - Scans the heap for inconsistencies, should exit with an assert
 * if an inconsistency is found.
 */

static freeblock_t *freeHead;
static header_t *firstHead;
static int num_freeblocks;

void mm_check() {
    //code is from discussion section
    header_t *h = firstHead;
    bool prev_alloc = !get_alloc(h);

    //assert prologue header is correct
    assert(get_below_header(h) == (header_t *) mem_heap_lo());

    //block level invariants
    while(get_size(h > 0)) {
        footer_t *f = get_footer(h);
        size_t size = get_size(h);
        //assert header and footer have the same size and allocation
        assert(get_size_footer(f) == size);
        //assert header and footer match
        assert((void *)f - size + sizeof(footer_t) == h);
        //assert no contiguous free blocks
        assert(prev_alloc != 0 && get_alloc(h) != 0);
        //assert size is aligned
        assert(size % ALIGNMENT == 0);
        assert((long) get_payload(h) % ALIGNMENT == 0);

        //assert header/footer stay inside the heap
        assert(h > mem_heap_lo() && h < mem_heap_hi());

        prev_alloc = get_alloc(h);
        h = get_above_header(h);
    }

    //assert epilogue is correct
    assert((void *) get_above_header(h) == mem_heap_hi() - 7);

    freeblock_t *fb = freeHead;
    freeblock_t *prev = freeHead->prev;
    freeblock_t *next = freeHead->next;
    int count = 0;

    //list level invariants
    while(fb) {
        count++;
        h = get_freeblock_header(fb);
        //assert block is actually free
        assert(!get_alloc(h));
        if(prev) {
            assert(prev->next == fb);
        }
        if(next) {
            assert(next->prev == fb);
        }
        assert(fb > mem_heap_lo() && fb < mem_heap_hi());

        fb = next;
    }

    //check for backwards cycle
    fb = prev;
    while(fb) {
        fb = fb->prev;
    }

    //assert number of free blocks in the list  = number of free blocks
    assert(count == num_freeblocks);

    return 0;
}

/*
    The extend_heap function ensures that additional heap space
    is retrieved from the memory and that the requested size is
    rounded properly
*/
static void *extend_heap(size_t words) {
    //code is borrowed from Computer Systems Textbook, Section 9.9
    //Dynamic Memory Allocation page 894, figure 9.45

    char *bp;
    size_t size;

    //allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long) (bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    //initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0));       /* free block header */
    PUT(FTRP(bp), PACK(size, 0));       /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       /* new epilogue header */

    //coalesce if the previous block was free
    return coalesce(bp);
}

/*
    The place function will split the block if the remainder
    of the block after splitting is still greater than or 
    equal to the minimum block size
*/
static void place(void *bp, size_t asize) {
    //code is based off of Computer Systems Textbook, Section 9.9
    //Dynamic Memory Allocation page 920

    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (DSIZE * 2)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize , 1));
    }

}

/*  The find_fit function searches for a free block that fits.
    The first while loop starts from the last search and check for the next
    free block that fits and the second while loop searches from the start
    until the last search.
*/
static void *find_fit(size_t asize) {
    //code is based off of Computer Systems Textbook, Section 9.9
    //Dynamic Memory Allocation page 920

    /* Next fit search */
    char * oldrover = rover;
    void *bp;

    //searches starting at last allocated block
    while(GET_SIZE(HDRP(rover))) {
        if(!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))) {
            return rover;
        }
        rover = NEXT_BLKP(rover);
    }

    bp = heap_listp;
    //searches starting from the beginning to the last search
    while(bp < oldrover) {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }

    return NULL;
}

//uses the boundary tag coalescing technique
//uses the four cases from the textbook and is implemented below
static void *coalesce(void *bp) {
    //code is based off of Computer Systems Textbook, Section 9.9
    //Dynamic Memory Allocation page 896, figure 9.46
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //case 1, next and prev both allocated
    if(prev_alloc && next_alloc) {
        return bp;
    }
    //case 2, prev is allocated, and next is free
    else if(prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    //case 3, prev is free and next is allocated
    else if(!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    //case 4, previous and next are free
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    //makes sure that rover is not pointing to a block that has been recently freed
    if((rover < NEXT_BLKP(bp)) && (rover > (char *)bp)) {
        rover = bp;
    }
    return bp;
}
