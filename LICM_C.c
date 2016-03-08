/*
 * File: LICM_C.c
 *
 * Description:
 *   Stub for LICM in C. This is where you implement your LICM pass.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* LLVM Header Files */
#include "llvm-c/Core.h"
#include "dominance.h"

/* Header file global to this project */
#include "cfg.h"
#include "loop.h"
#include "worklist.h"
#include "valmap.h"

static worklist_t list;

static LLVMBuilderRef Builder=NULL;

unsigned int LICM_Count=0;
unsigned int LICM_NoPreheader=0;
unsigned int LICM_AfterLoop=0;
unsigned int LICM_Load=0;
unsigned int LICM_BadCall=0;
unsigned int LICM_BadStore=0;


/*static void LICMOnFunction(LLVMValueRef funs){


}*/

valmap_t store_check,store_bad,store_bad2;





static int canMoveOutOfLoop(LLVMLoopRef L, LLVMValueRef I, LLVMValueRef funs, LLVMValueRef addr)
{
	
	LLVMValueRef iter1,iter2;
	worklist_t bblist1,bblist2,bblist3;
	LLVMBasicBlockRef bb_iter1,bb_iter2,bb_iter3;
  
  if(LLVMLoopContainsInst(L,addr)) // If addr is defined inside the loop and is a instruction
    return 0;

  if(LLVMIsAConstant(addr) || (LLVMIsAAllocaInst(addr))) //If addr is constant or allocainstruction
    {	
      bblist1 = LLVMGetBlocksInLoop(L);
      while(!worklist_empty(bblist1))
	{
	  bb_iter1 = (LLVMBasicBlockRef)worklist_pop(bblist1);
	  iter1 = LLVMGetFirstInstruction(bb_iter1);
	  while(iter1!=NULL)
	    {
	      if(LLVMIsACallInst(iter1))
		{
		      LICM_BadCall++;			 
		      return 0;
		}
	      if(LLVMIsAStoreInst(iter1))
		{
		  if(LLVMGetOperand(iter1,1)==addr) // Check for Store address
		    {
		      if(valmap_check(store_check,addr)) //Duplicate found do not increment BadStore
			{
			  return 0;
			}
		      else //Increment here
			{			
			  LICM_BadStore++;			 
			  valmap_insert(store_check,addr,LLVMGetOperand(iter1,0));
			  return 0;
			}
		    }
			LLVMValueRef bad_addr = LLVMGetOperand(iter1,1);
		  if(!LLVMIsAConstant(bad_addr) && !LLVMIsAAllocaInst(bad_addr)) // If address of Store is not constant and alloca instruction
		    {
			bad_addr = LLVMGetOperand(iter1,1);
		      if(valmap_check(store_bad,bad_addr))
			{
			  return 0;
			}
		      else
			{			
			 LICM_BadStore++;			 
			  valmap_insert(store_bad,bad_addr,LLVMGetOperand(iter1,0));
			  return 0;
			}
		    }
		}
	      iter1=LLVMGetNextInstruction(iter1);  
	    }
	}
    }
   else{ 
	 bblist3 = LLVMGetBlocksInLoop(L);
     	 while(!worklist_empty(bblist3))
	{
	  bb_iter3 = (LLVMBasicBlockRef)worklist_pop(bblist3);
	  iter2 = LLVMGetFirstInstruction(bb_iter3);
	  while(iter2!=NULL){
		if(LLVMIsAStoreInst(iter2)){
			if(valmap_check(store_bad2,LLVMGetOperand(iter2,1))){
				return 0;
			}
			else{
				LICM_BadStore++;
				valmap_insert(store_bad2,LLVMGetOperand(iter2,1),LLVMGetOperand(iter2,0));
				return 0;
			}
		}
		
		if(LLVMIsACallInst(iter2)){
			LICM_BadCall++;
			return 0;
		}
		 iter2=LLVMGetNextInstruction(iter2);
	 }
	 

   	}
   }
      
      

	
  

    bblist2 = LLVMGetExitBlocks(L);//Get exit basic blocks list check for dominance 
  while(!worklist_empty(bblist2))
    {
     bb_iter2 = (LLVMBasicBlockRef)worklist_pop(bblist2);
      if(!LLVMDominates(funs,LLVMGetInstructionParent(I),bb_iter2))
	return 0;
    }
  
    return 1;
 
      
 }


void LoopInvariantCodeMotion_C(LLVMModuleRef Module)
{
  LLVMValueRef funs,inst_iter;
  LLVMLoopInfoRef info;
  LLVMLoopRef i,temp,temp2;
  LLVMBasicBlockRef PH,bb_iter;
  LLVMBool a,b;
  store_check = valmap_create(); // Initialise the Maps needed for Store Mapping to Load Addresses
 store_bad = valmap_create();
 store_bad2 = valmap_create();


  Builder = LLVMCreateBuilder();

  list = worklist_create();

  for(funs=LLVMGetFirstFunction(Module);
      funs!=NULL;
      funs=LLVMGetNextFunction(funs))
    { 
      if (LLVMCountBasicBlocks(funs)){
      	info = LLVMCreateLoopInfoRef(funs);
	i = LLVMGetFirstLoop(info);
	while(i != NULL){
		 PH = LLVMGetPreheader(i);
		if(PH==NULL){
			LICM_NoPreheader++; //Counting the Preheaders of the loop
			i = LLVMGetNextLoop(info,i);
			continue;
		}
	//	printf("HELLO \n");
		worklist_t bb_list =  LLVMGetBlocksInLoop(i); //Getting Basic Blocks in a loop
		bb_iter = (LLVMBasicBlockRef)worklist_pop(bb_list); //Popping out one basic block out of a list of basic blocks
		while(!worklist_empty(bb_list)){
			//printf("CASECOMES HERE\n");
			//printf("CASE4\n");
			
			inst_iter = LLVMGetFirstInstruction(bb_iter); 
			//printf("CASE3\n");
			while(inst_iter != NULL){
				//printf("CASE1\n");
				temp = i;
				a = LLVMMakeLoopInvariant(temp,inst_iter); // Check for instructions other than store and load to make them invariant
				//b = LLVMIsValueLoopInvariant(temp,inst_iter);
				if(a){
					LICM_Count++;
					inst_iter = LLVMGetNextInstruction(inst_iter);
					//printf("CASE2\n");
					continue;

				}
				else{
					if(LLVMIsALoadInst(inst_iter) && !LLVMGetVolatile(inst_iter)){ //Check for Loads Now
						LLVMValueRef addr;
						addr = LLVMGetOperand(inst_iter,0);
					 	if(canMoveOutOfLoop(i,inst_iter,funs,addr)){ // If possible then this Load can be moved out else not
							LICM_Load++;
							LICM_Count++;
							LLVMBasicBlockRef bb_temp =  PH;
							LLVMValueRef j = LLVMGetLastInstruction(bb_temp); //Get branch of the Preheader 
							LLVMPositionBuilderBefore(Builder,j); //Position Builder before branch
							LLVMValueRef temp = inst_iter;
							LLVMValueRef clone = LLVMCloneInstruction(inst_iter);//Get the clone of instruction
							LLVMInsertIntoBuilder (Builder,clone); // Insert the clone into builder
							LLVMReplaceAllUsesWith(inst_iter,clone); // Replace uses with this clone
							inst_iter = LLVMGetNextInstruction(inst_iter); 
							LLVMInstructionEraseFromParent(temp);
							continue;
						}
					}					
				}
				inst_iter = LLVMGetNextInstruction(inst_iter);
			}
			//printf("CASE5\n");
			bb_iter = (LLVMBasicBlockRef)worklist_pop(bb_list);
		}
		
		i = LLVMGetNextLoop(info,i);
	}

      }
    }

  LLVMDisposeBuilder(Builder);
  Builder = NULL;

  fprintf(stderr,"LICM_Count      =%d\n",LICM_Count);
  fprintf(stderr,"LICM_NoPreheader=%d\n",LICM_NoPreheader);
  fprintf(stderr,"LICM_Load       =%d\n",LICM_Load);
  fprintf(stderr,"LICM_BadCall    =%d\n",LICM_BadCall);
  fprintf(stderr,"LICM_BadStore   =%d\n",LICM_BadStore);
}




