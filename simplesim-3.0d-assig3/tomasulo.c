
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         10

#define RESERV_INT_SIZE    4
#define RESERV_FP_SIZE     2
#define FU_INT_SIZE        2
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     4
#define FU_FP_LATENCY      9

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP) 

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;
static int instr_queue_head = 0;
static int instr_queue_tail = 0;

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//the index of the last instruction fetched
static int fetch_index = 0;

typedef struct instruction_list_type
{
  instruction_t *     node; //pointer to RS entry
  instruction_lst_t * next; //next itne

}instr_lst_t;

//The map table keeps track of which instruction produces the value for each register
static instr_lst_t * map_table[MD_TOTAL_REGS];


/* FUNCTIONAL UNITS */


/* RESERVATION STATIONS */

/* 
 * Description: 
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {

  /* ECE552: YOUR CODE GOES HERE */

  return true; //ECE552: you can change this as needed; we've added this so the code provided to you compiles
}

/* 
 * Description: 
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */

}


/* 
 * Description: 
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */

}

/* 
 * Description: 
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
}

/* 
 * Description: 
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {
  /* ECE552: YOUR CODE GOES HERE */
}

/* 
 * Description: 
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {
  /* ECE552: YOUR CODE GOES HERE */
  instruction_t f_instr;
  if (fetch_index == INSTR_TRACE_SIZE)
  {
    printf("INFO: reached the end of instruction trace execution ...\n");
    return;
  }

  //skip over TRAP instructions
  do {
    f_instr = trace->table[fetch_index++];
  } while(IS_TRAP(f_instr.op) && instr_queue_size != INSTR_QUEUE_SIZE);
  
  assert(instr_queue_head >= 0 && instr_queue_head < INSTR_QUEUE_SIZE);
  instr_queue[c_cnt_post_incr(instr_queue_head)] = f_instr; 
}

//update the MAP table during dispatch
void d_update_mt(instruction_t * d_instr)
{
  instr_lst_t *   mt_lst_entry, tmp_lst;
  //update MAP table
  if (d_instr->r_out[0] != DNA)
  {
     mt_lst_entry =  (instr_lst_t*)malloc(sizeof(instr_lst_t));
     mt_lst_entry->node = d_rs;
     mt_lst_entry->next = NULL;
     if (map_table[d_instr->r_out[0]] == NULL) {
       map_table[d_instr->r_out[0]] = mt_lst_entry;
     } else { //there is an existing map-table tag
       tmp_lst = map_table[d_instr->r_out[0]]
       while (tmp_lst->next != null) {
         tmp_lst = tmp_lst->next;
       }
       tmp_lst->next = mt_lst_entry;
     }
  } 
  if (d_instr->r_out[1] != DNA)
  {
     mt_lst_entry =  (instr_lst_t*)malloc(sizeof(instr_lst_t));
     mt_lst_entry->node = d_rs;
     mt_lst_entry->next = NULL;
     if (map_table[d_instr->r_out[1]] == NULL) {
       map_table[d_instr->r_out[1]] = mt_lst_entry;
     } else { //there is an existing map-table tag
       tmp_lst = map_table[d_instr->r_out[1]]
       while (tmp_lst->next != null) {
         tmp_lst = tmp_lst->next;
       }
       tmp_lst->next = mt_lst_entry;
     }
  } 
}
/* 
 * Description: 
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {
  /* ECE552: YOUR CODE GOES HERE */
  int i;
  instruction_t   d_instr;
  instruction_t * d_rs;
  fetch(trace);

  assert(instr_queue_tail >= 0 && instr_queue_tail < INSTR_QUEUE_SIZE);
  d_instr = instr_queue[c_cnt_post_incr(instr_queue_tail)]; 
  d_instr.tom_dispatch_cycle = current_cycle;

  if (USES_INT_FU(d_instr.op))
  {
    for(i=0; i<RESERV_INT_SIZE; ++i)
    {
      if (reservINT[i] == NULL) {
         d_rs = (instruction_t*) malloc(sizeof(instruction_t));
         *d_rs = d_instr;
         reservINT[i] = d_rs;
         break;
      }
    }
    printf("INFO: dispatched an INT instruction at cycle %d\n", current_cycle);
  }
  else if (USES_FP_FU(d_instr.op))
  {
    for(i=0; i<RESERV_FP_SIZE; ++i)
    {
      if (reservFP[i] == NULL) {
         d_rs = (instruction_t*) malloc(sizeof(instruction_t));
         *d_rs = d_instr;
         reservFP[i] = d_rs;
         break;
      }
    }
    printf("INFO: dispatched a FP instruction at cycle %d\n", current_cycle);
  }
  else if (IS_UNCOND_CTRL(d_instr.op) || IS_COND_CTRL(d_instr.op))
  {
    /*
    *  unconditional & conditional branches ar enot issued to the reservation stations
    *  they do not use any FU, they do not write to the CDB
    *  they do not cause a control hazard
    */
    printf("INFO: dispatched a branch instruction at cycle %d\n", current_cycle);
  }
  else
  {
    printf("WARNING: Unhandled instruction opcode at IFQ: %x, at cycle %d\n", d_instr.op, current_cycle);
  }


  //update map table
  d_update_mt(d_rs);

  //check for RAWs, update TAGs
  for (i = 0; i < 3; ++i)
  {
     //note: NULL value == free of RAW (i.e. tag)
     d_rs->Q[i] = map_table[r_in[i]]->node;
  } 

}

/* 
 * Description: 
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  //initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
      reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
      reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }
  
  int cycle = 1;
  while (true) {

     /* ECE552: YOUR CODE GOES HERE */
     cycle++;

     if (is_simulation_done(sim_num_insn))
        break;
  }
  
  return cycle;
}
