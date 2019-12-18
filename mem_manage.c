/**
 * This implementation uses a doubly linked free list, which is addressed by global pointers 'head' and 'tail.'
 * The free list is grown by appending in 'free'
 * malloc uses helper functions to attempt to find a free block of valid size using a first fit algorithm,
 *  if a block large enough is not found malloc will call a set of functions that call sbrk 
 *  to allocate apprpriate new space on the heap.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//block metadata
typedef struct block_head block_head;
struct block_head{
    size_t size;
    block_head *next;
    block_head *prev;
    int free;   //1 if free 0 if allocated
};

/**
 * globals
 * */

void *head; //head of block list
void *tail;
// int malloc_count;



/**
 * Helper functions
 * */

/**
 * Testing functions
 * */

/**
 * For testing purposes: prints text representation of block with size and allocated status
 **/
void printlist(){
    block_head *itr = head;
    printf("\n");
    while(itr){
        printf("[%d] %d->",itr->free, itr->size);
        itr = itr->next;
    }
    printf("\n");
}

/**
 * searches free list and returns block with appropriate size
 * **/
block_head *search_free(size_t size){
    // printf("search free\n");
    block_head *itr = (block_head*)head;
    //first fit
    while(itr){
        // printf("%d, %d: %d\n", itr->free, itr->size, size);
        if((itr->size>=size)){
            return itr;
        }
        itr = itr->next;
    }
    // printf("/search free\n");
    return NULL;

    // //best fit
    // int dif = -1;
    // int newdif = -1;
    // block_head *bestfit = NULL;
    // while(itr){
    //     newdif = (itr->size) - size;
    //     if(newdif>=0 && newdif<dif){
    //         dif = newdif;
    //         bestfit = itr;
    //     }
    //     itr = itr->next;
    // }
    // return bestfit;
}

/**
 * increase heap size, maintaining 8 byte alignment
 * returns pointer to beginning of newly allocated heap area
 * **/
block_head *inc_heap(size_t size){
    // printf("inc heap\n");
    block_head *block;
    size_t brksize = ALIGN(size);    //get aligned size to addr
    brksize += sizeof(block_head);
    block = sbrk(brksize);
    block->free = 0;    //malloc'd
    block->size = size;

    return block;
}

/**
 * removes block from free list
 * **/
void remove_block(block_head* remove){
    // printf("remove_block\n");
    if(!remove){
        printf("ERROR****: null ptr passed to remove_block");
        exit(EXIT_FAILURE);
    }
    if(remove==head){head=((block_head*)head)->next;}
    if(remove==tail){tail=((block_head*)tail)->prev;}
    if(remove->next){remove->next->prev=remove->prev;}
    if(remove->prev){remove->prev->next=remove->next;}
    // printf("/remove_block\n");
}

/**
 * coalesces adjacent blocks into large free block
 * runs in n^2 time where n = number of blocks in list
 * **/
void coalesce(){
    // printf("coalescing block\n ***");
    // printlist();
    //for block i in list
    block_head *itrx = (block_head*)head;
    while(itrx){
        //for block j in list
        block_head *itry = (block_head*)head;
        while(itry){
            if(itry==itrx){
                itry = itry->next;
                continue;
            }
            unsigned long mem_dif;
            if((unsigned long)itrx>(unsigned long)itry){    //y is first, create large block at y
                mem_dif = ((unsigned long)(itrx) - (unsigned long)(itry));  
                if(mem_dif <= (itry->size)+8+sizeof(block_head)){   //extra 8 bytes is for potential size alignment
                    remove_block(itrx);
                    itry->size = (itry->size) + (itrx->size);
                    return;
                }
            }else{
                mem_dif = ((unsigned long)(itry) - (unsigned long)(itrx));
                if(mem_dif <= (itrx->size)+8+sizeof(block_head)){
                    remove_block(itry);
                    itrx->size = (itry->size) + (itrx->size);
                    return;
                }
            }
            // printf("itry size: %d\n", itry->size);
            itry=itry->next;
        }
        // printf("itrx size: %d\n", itrx->size);
        itrx = itrx->next;
    }
    // printlist();
}


//"overload" for check to allow checking of specified range
int check_bounds(void *start, void *end){
    if(!start){
        printf("check: start node null\n");
        return -1;
    }
    int ret = 1;
    block_head *itr = (block_head*)start;
    block_head *fin = (block_head*)end;
    while(itr && itr!=fin){
        //check blocks are marked as free
        if(itr->free!=1){
            printf("MEM CHECK ERROR****: Block at ddress %p is not marked as free\n", itr);
            ret = -1;  
        }
        //check address is in heap range
        if(!((void*)itr)<sbrk(0)){
            printf("MEM CHECK ERROR****: Address %p lies outside the heap\n", itr);
            ret = -1;
        }
        //check block is valid
        if(!(0<itr->size && itr->size<10000)){    //since all blocks in trace files are <10,000
            printf("MEM CHECK ERROR****: Block at address %p is invalid\n", itr);
            ret = -1;
        }
        itr = itr->next;
    }
    printf("Heap consistency check completed. See any above errors\n");
    return ret;
}

/**
 * heap consistency checker
 * checks from param start to param end; check(void) will call (head, tail) to check whole list
 * assumes params can be cast to valid block pointers or NULL
 * returns 1 on success -1 on error
 **/
int check(){
    return check_bounds(head, tail);
}


/**
 * memory management functions: 
 * */

/* 
 * init - initialize the malloc package.
 */
int init(void){
    // printf("init\n");
    head = (block_head*)NULL;
    tail = (block_head*)NULL;
    // printf("/init\n");
    return 0;
}

/* 
 * malloc - allocates block of size 'size' in free block or new heap space
 * returns pointer to newly allocated payload
 */
void *malloc(size_t size){
    // printf("malloc\n");
    block_head *block;
    block = search_free(size);
    if(!block){ //no block found - append to list
        block = inc_heap(size);
    }else{
        // printf("found free, %d\n", block->size);
        remove_block(block);    //remove from free list
    }
    // printlist();
    return (block+1);
}

/* 
 * free - frees payload pointed at by param 'ptr'
 * appends new block to end of free list
 * calls coalesce after new block has been inserted
 */
void free(void *ptr){
    // printf("free\n");
    if(!ptr){
        printf("ERROR** null ptr passed to free");
        return;
    }
    block_head *block = (block_head*)ptr-1;
    // printf("freeing size %d\n", block->size);
    block->free = 1;
    block->next = NULL;
    block->prev = tail;
    if(!head){
        head = block;
        tail = block;
    }else{
        if(tail){((block_head*)tail)->next = block;}
        tail = block;
    }
    // coalesce();
    // printlist();
}


void *realloc(void *ptr, size_t size){

    block_head *newblock = malloc(size);
    block_head *oldblock = (block_head*)ptr-1;
    if (newblock == NULL || oldblock == NULL){
      return NULL;
    }
    if(size < oldblock->size){
        memcpy(newblock, ptr, ALIGN(size));
    }else{
        memcpy(newblock, ptr, ALIGN(oldblock->size));
    }
    free(ptr);
    return newblock;
}