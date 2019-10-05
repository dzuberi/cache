#include "cachesim.hpp"
#include <map>
#include <vector>
#include <assert.h>
#include <algorithm>
#include <iostream>
#include <stdio.h>
#include <string.h>
//block structure that will be used for the whole cache
struct Block_ {
    int valid;
    uint64_t tag;
    int dirty;
    uint64_t lru;
};
//each block in the prefetch buffer has a tag, valid bit, and timestamp for FIFO implementation
struct p_block {
	int valid;
	uint64_t tag;
	uint64_t fifo;
};
//each row of markov will have a timestamp for LRU and a table of addresses & uses
struct markov_row {
	uint64_t pre_miss;
	uint64_t table[2][4]; //[0][i] is the ID of the i'th block, [1][i] is the count
	uint64_t timestamp;
};

uint64_t accessNum = 0;

//array for cache
struct Block_ **cache;
struct markov_row *markov;
struct p_block *p_buffer;
int numWays;
int numSets;

uint64_t C;
uint64_t B;
uint64_t S;
int markovDepth = 0;
uint64_t numHits = 0;
uint64_t numMiss = 0;
uint64_t numWrites = 0;
uint64_t numWriteMiss = 0;
uint64_t numWriteHits = 0;
uint64_t numWriteBack = 0;
uint64_t numReads = 0;
uint64_t numReadMiss = 0;
uint64_t numReadHits = 0;
uint64_t prefetchHits = 0;
uint64_t numPrefetch = 0;
uint64_t pbufferMiss = 0;
uint64_t prefetchIssued = 0;
uint64_t numMissL1 = 0;
int pbufferlength = 32;
double hitTime = 0.0;
double missTime = 0.0;
double currTime = 0.0;
uint64_t preType = 0;
uint64_t prevMiss = 0;
int firstMiss = 1;

/**
 * Subroutine for initializing the cache. You many add and initialize any global or heap
 * variables as needed.
 * XXX: You're responsible for completing this routine
 *
 * @c1 The total number of bytes for data storage in L1 is 2^c
 * @b1 The size of L1's blocks in bytes: 2^b-byte blocks.
 * @s1 The number of blocks in each set of L1: 2^s blocks per set.
 */

void setup_cache(uint64_t c1, uint64_t b1, uint64_t s1, uint64_t p1, uint64_t prefetcher_type) {
	C = c1; B=b1; S=s1; markovDepth=(int) p1; preType = prefetcher_type;
	//number of ways is equal to 2^S
	numWays = 1 << S;
	//number of sets is equal to 2^(C-B-S)
	numSets = 1 << (C-B-S);

	//create 2D array of blocks for cache
	cache = (Block_**)malloc(numSets * sizeof(Block_*));
	for(int i = 0; i < numSets; i++){
		cache[i] = (Block_*)malloc(numWays * sizeof(Block_));
		for(int j = 0; j < numWays; j++){
			cache[i][j] = {.valid = 0, .tag = 0, .dirty = 0, .lru=0};
		}
	}
	//create markov and prefetch buffer objects
	markov = (markov_row*)malloc(markovDepth * sizeof(markov_row));
	memset(markov, 0, markovDepth*sizeof(markov_row));
	p_buffer = (p_block*)malloc(pbufferlength * sizeof(p_block));
	for(int i = 0; i < pbufferlength; i++){
		p_buffer[i] = {.valid = 0, .tag = 0, .fifo = 0};
	}
	//set the hit time and initialize the time as 0
	hitTime = 2 + 0.2*(double)S;
	missTime = 20.0;
	currTime = 0.0;
}

/**
 * Subroutine that simulates the cache one trace event at a time.
 * XXX: You're responsible for completing this routine
 *
 * @type The type of event, can be READ or WRITE.
 * @arg  The target memory address
 * @p_stats Pointer to the statistics structure
 */
void cache_access(char type, uint64_t arg, cache_stats_t* p_stats) {
	//printf("Time: %d\n",accessNum);
	//increment access number
	accessNum += 1;
	//increment number of reads or writes
	if(type == READ){
		numReads += 1;
	}
	else numWrites += 1;

	int cacheHit = 0;
	int preHit = 0;
	//set mask for index, which will be all 1's at the index bit and 0 everywhere else
	uint64_t indexmask = ((1 << (C-B-S)) - 1) << B;
	int index = (int)((arg & indexmask) >> B);
	//set mask for tag, which will be all 1's at the bits before the index bits and 0 everywhere else. This could also be shifted all the way right, but is unnecessary since we are using uint64_t
	uint64_t tagmask = ~((1 << (B + (C-B-S))) - 1);
	uint64_t tag = arg & tagmask;

	uint64_t blockid = (arg & tagmask) | (arg & indexmask); //this will be used in the FA prefetch buffer
	uint64_t nPlusOne = blockid + (1 << B);
	int prefetchIndex = -1;
	//printf("Curr Addr without offset: %llx\n",blockid);
	//loop through all the ways in the indexed set to see if the tag matches.
	for(int j = 0; j < numWays; j++){
		if((cache[index][j].tag == tag) && (cache[index][j].valid==1)) {
			//if the tag matches, print hit and increment the number of hits based on the type
			printf("H\n");
			cacheHit = 1;
			numHits += 1;
			//set lru to the access number to record when it was last used
			cache[index][j].lru = accessNum;
			if(type == WRITE){
				//if the hit is a write, the dirty bit need to be set
				cache[index][j].dirty = 1;
				numWriteHits += 1;
			}
			else numReadHits += 1;
		}
		//if it misses in the cache, check prefetch buffer (unless there is no prefetching)
		else if (preType > 0) {
			for(int i=0; i<pbufferlength; i++){
				if((p_buffer[i].tag == blockid) && (p_buffer[i].valid == 1)){
					prefetchIndex = i;
					prefetchHits += 1;
					preHit = 1; //flag set
					p_buffer[i].valid = 0; //if it is found in the prefetch buffer, move to cache
					printf("PH\n");
					break; //no reason to continue loop
				}
			}
		}
	}
	uint64_t p_tag;
	if(cacheHit == 0){
		
		if (preHit == 0){ //if it isn't found in either cache or prefetch
			pbufferMiss += 1;
			int preReplace = -1;
			//this loop finds the prefetch block that will be replaced if prefetching is required
			uint64_t fifotest = std::numeric_limits<uint64_t>::max();
			for(int i=0; i<pbufferlength; i++){ 
				if (p_buffer[i].valid == 0){
					preReplace = i;
					break;
				}
				else if (p_buffer[i].fifo < fifotest){
					preReplace = i;
					fifotest = p_buffer[i].fifo;
				}
			}
			int replacing = 0;

			//work here
			int tempIndex = -1;
			//this searches the markov table if markov or hybrid is enabled
			if((preType == 1)||(preType == 3)){
				int mfuIndex = 0;
				uint64_t mfuValue = 0;
				uint64_t mfuAddr = 0;
				replacing = 0;
				//first search the rows to see if any match the current block
				for(int i=0; i<markovDepth; i++){
					if(markov[i].pre_miss == blockid){
						tempIndex = i;
						//if the row is found, find the MFU to prefetch
						for(int j=0; j<4; j++){
							if(markov[i].table[1][j] > mfuValue){
								mfuIndex = j;
								mfuAddr = markov[i].table[0][j];
								mfuValue = markov[i].table[1][j];
								replacing = 1;
							}
							//if the MFU's are equal, prefetch the higher address
							else if(markov[i].table[1][j] == mfuValue){
								if((mfuAddr < markov[i].table[0][j]) && (mfuValue > 0)){
									mfuAddr = markov[i].table[0][j];
									mfuIndex = j;
									mfuValue = markov[i].table[1][j];
									replacing = 1;
								}
							}
						}
					}
				}
				p_tag = mfuAddr;
				if(p_tag == blockid) replacing = 0;
				//printf("%d,%d,%d\n",tempIndex,mfuIndex,replacing);
			}
			//if n+1, or hybrid and not found in markov table, prefetch n+1
			if((preType == 2)||((preType == 3)&& (replacing == 0))){
				p_tag = nPlusOne;
				replacing = 1;
			}
			//if it is already in the prefetch buffer, don't prefetch
			for (int i = 0; i<pbufferlength; i++){
				if ((p_buffer[i].valid == 1) && (p_buffer[i].tag == p_tag)){
					replacing = 0;
					//printf("in prefetch buffer\n");
				}
			}
			//mask the prefetch index to search cache
			int p_index = (int)((p_tag & indexmask) >> B);
			uint64_t p_cachetag = p_tag & tagmask;
			//if it is found in the cache, don't prefetch
			for(int j=0; j < numWays; j++){
				if((cache[p_index][j].tag == p_cachetag) && (cache[p_index][j].valid == 1)){
					replacing = 0;
					//printf("in cache\n");
				}
			}
			//always print miss if it is not found in prefetch buffer or 
			printf("M\n");
			//if we are prefetching, prefetch
			if(replacing == 1){
				if(preType == 1){
					//markov[tempIndex].timestamp = accessNum;
					//printf("%d\n",tempIndex);
					//printf("Issue prefetch for addr: %llx\n",p_tag);
				}
				prefetchIssued += 1;
				//set fifo bit and tag, make valid
				p_buffer[preReplace] = {.valid = 1, .tag = p_tag, .fifo = accessNum};
			}
			numMiss += 1;
			currTime = currTime + missTime;
			//if markov or hybrid, and this is not the first miss, update markov table
			if(((preType == 1)||(preType == 3))&&(firstMiss == 0)){
				//printf("Prev Miss Addr without offset: %llx\n",prevMiss);
				int row = -1;
				int column = -1;
				uint64_t lfuVal = std::numeric_limits<uint64_t>::max();
				int lfuIndex = -1;
				uint64_t lfuAddr = std::numeric_limits<uint64_t>::max();
				//search for row
				for (int i=0 ; i<markovDepth ; i++){
					if (markov[i].pre_miss == prevMiss){
						row = i;
						//printf("Row hit\n");
						//search for column
						for (int j=0; j<4; j++){
							if (markov[i].table[0][j] == blockid){ //row exists, column exists
								column = j;
								//markov[i].table[1][j] += 1;
								//printf("Column hit\n");
							}
						}
						//if column not found, find one to replace
						if (column < 0){ //column doesnt exist
							for(int j=0; j<4; j++){
								if(markov[i].table[1][j] < lfuVal){
									lfuVal = markov[i].table[1][j];
									lfuIndex = j;
									lfuAddr = markov[i].table[0][j];
								}
								else if(markov[i].table[1][j] == lfuVal){
									if(markov[i].table[0][j] < lfuAddr){
										lfuVal = markov[i].table[1][j];
										lfuIndex = j;
										lfuAddr = markov[i].table[0][j];
									}
								}
							}
							//replace column
							column = lfuIndex;
							markov[row].table[0][column] = blockid;
							markov[row].table[1][column] = 0;
							//printf("Column miss\n");
						}
					}
					else;
				}
				int lruRow = -1;
				uint64_t lruTime = std::numeric_limits<uint64_t>::max();
				//if row not found, find one to replace
				if (row < 0){ //row and column dont exist
					for(int i=0; i<markovDepth; i++){
						if(markov[i].timestamp < lruTime){
							lruTime = markov[i].timestamp;
							row = i;
						}
					}
					//replace row
					markov[row].pre_miss = prevMiss;
					//kill old row
					for(int i=0; i<4; i++){
						markov[row].table[0][i] = 0;
						markov[row].table[1][i] = 0;
					}
					column = 0;
					//markov[row].table[0][column] = blockid;
					//rintf("Row miss\nColumn miss\n");
				}
				markov[row].table[0][column] = blockid;
				markov[row].timestamp = accessNum;
				markov[row].table[1][column] += 1;
				//printf("markov:%d,%d,%d,%d\n",row,column,lfuVal,lfuAddr);
			}
			prevMiss = blockid;
			firstMiss = 0;
		}

		numMissL1 += 1;

		//now update the cache
		int lruIndex = 0;
		//set current lru to the highest possible value of uint64_t

		uint64_t currMin = std::numeric_limits<uint64_t>::max();
		//loop through the LRU values. If any value is lower, replace
		for(int j=0; j < numWays; j++){
			uint64_t jlru = cache[index][j].lru;
			if(jlru < currMin){ //could add in a check for valid bits, but unnecessry since all new blocks had lru time set to 0.
				currMin = jlru;
				lruIndex = j;
			}
		}

		if(cache[index][lruIndex].dirty == 1){
			//if the replaced block has a dirty bit of 1, write back
			numWriteBack += 1;
		}

		cache[index][lruIndex] = {.valid = 1, .tag = tag, .dirty = 0, .lru=accessNum};
		if(type==WRITE){
			//if write, set dity bit
			cache[index][lruIndex].dirty = 1;

			numWriteMiss += 1;

		}
		else {
			numReadMiss += 1;	
		}



	}
	//add hit time to all
	currTime = currTime + hitTime;
}

/**
 * Subroutine for cleaning up any outstanding memory operations and calculating overall statistics
 * such as miss rate or average access time.
 * XXX: You're responsible for completing this routine
 *
 * @p_stats Pointer to the statistics structure
 */
void complete_cache(cache_stats_t *p_stats) {
		//free cache
	for (int i=0; i<numSets; i++){
		free(cache[i]);
	}
	free(cache);
	free(markov);
	free(p_buffer);
	
	//set all of the values in the p_stats structure
	p_stats -> accesses = numHits + numMiss + prefetchHits;
	p_stats -> prefetch_issued = prefetchIssued;
	p_stats -> prefetch_hits = prefetchHits;
	p_stats -> prefetch_misses = pbufferMiss;
	p_stats -> accesses_l2 = 0; //no L2
	p_stats -> accesses_vc = 0; //no victim cache
	p_stats -> reads = numReads;
	p_stats -> read_hits_l1 = numReadHits;
	p_stats -> read_misses_l1 = numReadMiss;
	p_stats -> read_misses_l2 = 0; //no L2
	p_stats -> writes = numWrites;
	p_stats -> write_hits_l1 = numWriteHits;
	p_stats -> write_misses_l1 = numWriteMiss;
	p_stats -> write_misses_l2 = 0;  //no L2
	p_stats -> write_back_l1 = numWriteBack;
	p_stats -> write_back_l2 = 0;  //no L2
	p_stats -> total_hits_l1 = numHits;
	p_stats -> total_misses_l1 = numWriteMiss + numReadMiss;
	p_stats -> l1_hit_ratio = ((double)numHits)/((double)(numHits+numMiss+prefetchHits));
	p_stats -> l1_miss_ratio = ((double)numMissL1)/((double)(numHits+numMiss+prefetchHits));
	p_stats -> overall_miss_ratio = (double)(numHits+numMiss+prefetchHits-numHits-prefetchHits)/(double)(numHits+numMiss+prefetchHits);
	p_stats -> read_hit_ratio = ((double)numReadHits)/((double)(numReadHits+numReadMiss));
	p_stats -> read_miss_ratio = ((double)numReadMiss)/((double)(numReadHits+numReadMiss));
	p_stats -> write_hit_ratio = ((double)numWriteHits)/((double)(numWriteHits+numWriteMiss));
	p_stats -> write_miss_ratio = ((double)numWriteMiss)/((double)(numWriteHits+numWriteMiss));
	p_stats -> prefetch_hit_ratio = (double)prefetchHits / (double)prefetchIssued;
	p_stats -> victim_hits = 0;
	p_stats -> avg_access_time_l1 = currTime / (double) accessNum;
	if(preType == 0){
		p_stats -> prefetch_hit_ratio = 0.00;
		p_stats -> prefetch_misses = 0;
		p_stats -> prefetch_hits = 0;
	}

}