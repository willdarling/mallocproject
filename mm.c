/* 
 * mm.c -  explicit free list allocator with first fit replacement
 */
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* $begin mallocmacros */
/* Basic constants and macros */  
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define MINIMUM     24      /* minimum block size, to include space for
                               linked list pointers (bytes)  */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p)) 
#define PUT(p, val)  (*(unsigned int *)(p) = (val))  

/* Read and write an address at p */
#define SUCC(bp)   (*(void **)(bp+DSIZE))
#define PRED(bp)   (*(void **)(bp))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((void *)(bp) - WSIZE)  
#define FTRP(bp)       ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((void *)(bp) + GET_SIZE(((bp) - WSIZE)))
#define PREV_BLKP(bp)  ((void *)(bp) - GET_SIZE(((bp) - DSIZE)))


/* single word (4), double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* pointer to first block in heap list */  
static char *free_listp = 0;  /* pointer to first block address in free list */

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);
static void fcons(void *bp);
static void fremove(void *bp);

/* 
 * mm_init - Initialize the memory manager
 * 
 * return 0 if successful, -1 if failure.
 */
/* $begin mm_init */
int mm_init(void) 
{
  //printf("mm_init\n");
  /* create the initial empty heap */
  if ((heap_listp = mem_sbrk(2*MINIMUM)) == NULL)
    return -1;

  PUT(heap_listp, 0);                          /* alignment padding */
  PUT(heap_listp + WSIZE, PACK(MINIMUM, 1));   /* prologue header */ 
  PUT(heap_listp + DSIZE, 0);                  /* pred pointer */
  PUT(heap_listp + DSIZE+WSIZE, 0);            /* succ pointer */
  PUT(heap_listp + MINIMUM, PACK(MINIMUM, 1)); /* prologue footer */ 
  PUT(heap_listp + MINIMUM+WSIZE, PACK(0, 1)); /* epilogue header */

  free_listp = heap_listp + DSIZE;   /* adjust free_listp to be the succ pointer of the prologue header */
  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;

  return 0;
}
/* $end mm_init */

/*
 * malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
  //printf("mm_malloc\n");
  size_t asize;      /* adjusted block size */
  size_t extendsize; /* amount to extend heap if no fit */
  char *bp;    

  /* Ignore spurious requests */
  if (size <= 0)
    return NULL;

  /* Adjust block size to include overhead and alignment reqs. */
  asize = MAX(ALIGN(size) + DSIZE, MINIMUM);

  /* Search the free list for a fit */
  if ((bp = find_fit(asize))) {
    place(bp, asize);
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
    return NULL;
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
  //printf("mm_free\n");
  if(bp == 0) return;   /* Ignore free(NULL) */
  
  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);
}
/* $end mmfree */

/*
 * mm_realloc - naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
  //printf("mm_realloc\n");
  size_t oldsize;
  size_t asize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size <= 0) {
    mm_free(ptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(ptr == NULL) {
    return mm_malloc(size);
  }

  oldsize = GET_SIZE(HDRP(ptr));
  asize = MAX(ALIGN(size) + DSIZE, MINIMUM);

  /* If the block size doesn't need to be changed, return the pointer */
  if(oldsize == asize) {
    return ptr;
  }

  if(asize < oldsize) {
    
    if(oldsize - asize <= MINIMUM) {
      return ptr;
    }
    PUT(HDRP(ptr), PACK(asize, 1));
    PUT(FTRP(ptr), PACK(asize, 1));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldsize-asize, 1));
    mm_free(NEXT_BLKP(ptr));
    return ptr;
  }

  newptr = mm_malloc(size);

  if(!newptr) {
    return 0;
  }

  /* Copy the old data. */
  if(size < oldsize) oldsize = size;
  memcpy(newptr, ptr, oldsize);

  /* Free the old block. */
  mm_free(ptr);

  return newptr;
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
void mm_checkheap(int verbose)
{
  //printf("mm_checkheap\n");
  void *bp = heap_listp;

  if (verbose)
    printf("Heap (%p):\n", heap_listp);

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose) 
      printblock(bp);
    checkblock(bp);
  }

  if (verbose)
    printblock(bp);
  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
    printf("Bad epilogue header\n");
}

/* 
 * extend_heap - Extend heap with free block, add the free block onto 
 * the free list and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
  //printf("extend_heap\n");
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  size = size < MINIMUM ? MINIMUM : size;
  /* Get the physical block and error check */
  if ((long)(bp = mem_sbrk(size)) == -1) 
    return NULL;

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

  return coalesce(bp);
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static void place(void *bp, size_t asize)
{
  //printf("place\n");
  size_t csize = GET_SIZE(HDRP(bp));

  if ((csize - asize) >= (MINIMUM)) { 
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    fremove(bp);
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
    coalesce(bp);
  }
  else { 
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
    fremove(bp);
  }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{ 
  //printf("find_fit\n");
  /* first fit search */ 
  void *bp;
              /* for loop ends at prologue (which is the permanent tail) */
  for(bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = SUCC(bp)) { 
    if (asize <= (size_t) GET_SIZE(HDRP(bp))) {
      return bp;
    }
  }  

  return NULL; /* no fit */
}

/*
 * coalese - boundary tag coalescing. Return ptr to coalesced block
 */
 
static void *coalesce(void *bp) 
{
  //printf("coalesce\n");
  size_t prev_alloc;
  prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) {                /* Case 1 */
      fcons(bp);
    return bp;
  }

  if (prev_alloc && !next_alloc) {               /* Case 2 */
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    fremove(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }

  else if (!prev_alloc && next_alloc) {          /* Case 3 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    bp = PREV_BLKP(bp);
    fremove(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }

  else {                                        /* Case 4 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
        GET_SIZE(HDRP(NEXT_BLKP(bp)));
    fremove(PREV_BLKP(bp));
    fremove(NEXT_BLKP(bp));
    bp = PREV_BLKP(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  fcons(bp);
  return bp;
}

/*
 * fcons - fcons the free block onto the head of the free_list 
 */
void fcons(void *bp)
{
  //printf("fcons\n");
  SUCC(bp) = free_listp; /* set bp successor */
  PRED(free_listp) = bp; /* update head predecessor */
  PRED(bp) = NULL; /* set bp predecessor */
  free_listp = bp; /* update head global */
}

/*
 * fremove - fremove the free block from the free list 
 */
void fremove(void *bp)
{
  //printf("fremove\n");
  if (PRED(bp)) {
    SUCC(PRED(bp)) = SUCC(bp);
  }
  else {
    free_listp = SUCC(bp); 
  }
  PRED(SUCC(bp)) = PRED(bp);

}

static void printblock(void *bp) 
{
  //printf("printblock\n");
  size_t hsize;//, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  //halloc = GET_ALLOC(HDRP(bp));  
  //fsize = GET_SIZE(FTRP(bp));
  //falloc = GET_ALLOC(FTRP(bp));  

  if (hsize == 0) {
    //printf("%p: EOL\n", bp);
    return;
  }

  /*  //printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp, 
      hsize, (halloc ? 'a' : 'f'), 
      fsize, (falloc ? 'a' : 'f')); */
}

static void checkblock(void *bp) 
{
  //printf("checkblock\n");
  if ((size_t)bp % 8)
    printf("Error: %p is not doubleword aligned\n", bp);
  if (GET(HDRP(bp)) != GET(FTRP(bp)))
    printf("Error: header does not match footer\n");
}

/*
 * mm_calloc
 */
void *mm_calloc (size_t nmemb, size_t size)
{
  //printf("mm_calloc\n");
  void *ptr;
  if (heap_listp == 0){
    mm_init();
  }

  ptr = mm_malloc(nmemb*size);
  memset(ptr, 0, nmemb*size);
  return ptr;
}
