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
  instruction_t                * node; //pointer to RS entry
  struct instruction_list_type * next; //next itne
} instr_lst_t;

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
  /* ECE552: Assignment 3 - BEGIN CODE */

  return false;
  /* ECE552: Assignment 3 - END CODE */
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
  /* ECE552: Assignment 3 - BEGIN CODE */
  int i;

  //free the RS of an entry
  for (i=0; i<RESERV_INT_SIZE; i=i+1) {
     if(reservINT[i]->tom_cdb_cycle == current_cycle) {
       reservINT[i] = NULL;
       break;
     }
  }
  for (i=0; i<RESERV_FP_SIZE; i=i+1) {
     if(reservFP[i]->tom_cdb_cycle == current_cycle) {
       reservFP[i] = NULL;
       break;
     }
  }

  /* ECE552: Assignment 3 - END CODE */
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
  /* ECE552: Assignment 3 - BEGIN CODE */
  int i, cdb_cycle; 
  int fu_idx = -1;
  bool fp_fu = false;

  instruction_t * c_instr = NULL;
  for(i=0; i<FU_INT_SIZE; i=i+1)
  {
    if (fuINT[i] != NULL && fuINT[i]->tom_execute_cycle > 0) {
       cdb_cycle = fuINT[i]->tom_execute_cycle + 4;
       if(cdb_cycle <= current_cycle) {
         if(c_instr == NULL) {
           c_instr = fuINT[i];
           fu_idx = i;
         } else if(fuINT[i]->tom_dispatch_cycle < c_instr->tom_dispatch_cycle) {
           c_instr = fuINT[i];
           fu_idx = i;
         }
       }
    }
  }
  for(i=0; i<FU_FP_SIZE; i=i+1)
  {
    if (fuFP[i] != NULL && fuFP[i]->tom_execute_cycle > 0) {
       cdb_cycle = fuFP[i]->tom_execute_cycle + 9;
       if(cdb_cycle <= current_cycle) {
         if(c_instr == NULL) {
           c_instr = fuFP[i];
           fu_idx = i;
           fp_fu = true;
         } else if(fuFP[i]->tom_dispatch_cycle < c_instr->tom_dispatch_cycle) {
           c_instr = fuFP[i];
           fu_idx = i;
           fp_fu = true;
         }
       }
    }
  }
  if (c_instr == NULL)
    return;
  c_instr->tom_cdb_cycle = current_cycle; 

  //clear FU, RS of the completed instruction
  if(fp_fu) {
   fuFP[fu_idx] = NULL;
  } else {
   fuINT[fu_idx] = NULL;
  }

  /* ECE552: Assignment 3 - END CODE */
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
  /* ECE552: Assignment 3 - BEGIN CODE */
  int i; 

  for(i=0; i<FU_INT_SIZE; i=i+1)
  {
    if (fuINT[i] != NULL && fuINT[i]->tom_execute_cycle == 0)
       fuINT[i]->tom_execute_cycle = current_cycle;
  }

  for(i=0; i<FU_FP_SIZE; i=i+1)
  {
    if (fuFP[i] != NULL && fuFP[i]->tom_execute_cycle == 0)
       fuFP[i]->tom_execute_cycle = current_cycle;
  }
  /* ECE552: Assignment 3 - END CODE */
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
  /* ECE552: Assignment 3 - BEGIN CODE */
  int i, j;
  instruction_t * i_instr = NULL;
  instruction_t * tmp = NULL;

  //check for an available INT FU
  for(i=0; i<FU_INT_SIZE; i=i+1)
  {
    if (fuINT[i] == NULL)
    {
       i_instr = NULL; 
       //select the oldest instruction in RS tables that is ready to exec.
       for(j=0; j<RESERV_INT_SIZE; j=j+1)
       {
          tmp = reservINT[j];
          //NULL & RAW check -- continue if a tag is not NULL
          if(tmp == NULL || tmp->Q[0] || tmp->Q[1] || tmp->Q[2])
            continue;
          assert(tmp->tom_dispatch_cycle > 0);

          //select not yet issued RS entry
          if (tmp->tom_issue_cycle == 0) {
             if(i_instr == NULL)
               i_instr = tmp; 
             else if (tmp->tom_dispatch_cycle < i_instr->tom_dispatch_cycle)
               i_instr = tmp; 
          }
       }
       if(i_instr == NULL)
         continue;
       i_instr->tom_issue_cycle = current_cycle;
       fuINT[i] = i_instr;
    }
  }
  //check for an available FP FU
  for(i=0; i<FU_FP_SIZE; i=i+1)
  {
    if (fuFP[i] == NULL)
    {
       i_instr = NULL; 
       for(j=0; j<RESERV_FP_SIZE; j=j+1)
       {
          tmp = reservFP[j];
          //NULL & RAW check -- continue if a tag is not NULL
          if(tmp == NULL || tmp->Q[0] || tmp->Q[1] || tmp->Q[2])
            continue;
          assert(tmp->tom_dispatch_cycle > 0);

          //select not yet issued RS entry
          if (tmp->tom_issue_cycle == 0) {
             if(i_instr == NULL)
               i_instr = tmp; 
             else if (tmp->tom_dispatch_cycle < i_instr->tom_dispatch_cycle)
               i_instr = tmp; 
          }
       }
       if(i_instr == NULL)
         continue;
       i_instr->tom_issue_cycle = current_cycle;
       fuFP[i] = i_instr;
    }
  }
  /* ECE552: Assignment 3 - END CODE */
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
  /* ECE552: Assignment 3 - BEGIN CODE */
  instruction_t * f_instr;

  if (fetch_index == INSTR_TRACE_SIZE)
  {
    printf("INFO: reached the end of instruction trace execution ...\n");
    return true;
  }

  //IFQ full
  if (instr_queue_size == INSTR_QUEUE_SIZE)
     return;
 
  //skip over TRAP instructions
  do {
    f_instr = get_instr(trace, fetch_index++);
  } while(IS_TRAP(f_instr->op) && instr_queue_size <= INSTR_QUEUE_SIZE);

  assert(instr_queue_head >= 0 && instr_queue_head < INSTR_QUEUE_SIZE);

  instr_queue[instr_queue_head++] = f_instr; 
  if (instr_queue_head == INSTR_QUEUE_SIZE)
     instr_queue_head = 0; 
  ++instr_queue_size;
  /* ECE552: Assignment 3 - END CODE */
}

/* ECE552: Assignment 3 - BEGIN CODE */
//update the MAP table during dispatch
void d_update_mt(instruction_t * d_instr)
{
  instr_lst_t *mt_lst_entry;
  instr_lst_t *tmp_lst;

  //update MAP table
  if (d_instr->r_out[0] != DNA)
  {
     mt_lst_entry = (instr_lst_t *)malloc(sizeof(instr_lst_t));
     mt_lst_entry->node = d_instr;
     mt_lst_entry->next = NULL;
     if (map_table[d_instr->r_out[0]] == NULL) {
       map_table[d_instr->r_out[0]] = mt_lst_entry;
     } else { //there is an existing map-table tag
       tmp_lst = map_table[d_instr->r_out[0]];
       while (tmp_lst->next != NULL) {
         tmp_lst = tmp_lst->next;
       }
       tmp_lst->next = mt_lst_entry;
     }
  } 
  if (d_instr->r_out[1] != DNA)
  {
     mt_lst_entry = (instr_lst_t*)malloc(sizeof(instr_lst_t));
     mt_lst_entry->node = d_instr;
     mt_lst_entry->next = NULL;
     if (map_table[d_instr->r_out[1]] == NULL) {
       map_table[d_instr->r_out[1]] = mt_lst_entry;
     } else { 
       //there is an existing map-table tag; append tag at the list tail
       tmp_lst = map_table[d_instr->r_out[1]];
       while (tmp_lst->next != NULL) {
         tmp_lst = tmp_lst->next;
       }
       tmp_lst->next = mt_lst_entry;
     }
  } 
}
/* ECE552: Assignment 3 - END CODE */

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
  /* ECE552: Assignment 3 - BEGIN CODE */
  int i;
  instruction_t * d_rs;
  fetch(trace);

  assert(instr_queue_tail >= 0 && instr_queue_tail < INSTR_QUEUE_SIZE);
  assert(instr_queue_size > 0 && instr_queue_size <= INSTR_QUEUE_SIZE);

  d_rs = instr_queue[instr_queue_tail--]; 
  if (instr_queue_tail < 0)
     instr_queue_tail = INSTR_QUEUE_SIZE - 1;
  --instr_queue_size;

  d_rs->tom_dispatch_cycle = current_cycle;

  if (USES_INT_FU(d_rs->op))
  {
    for(i=0; i<RESERV_INT_SIZE; ++i)
    {
      if (reservINT[i] == NULL) {
         reservINT[i] = d_rs;
         break;
      }
    }
    printf("INFO: dispatched an INT instruction at cycle %d\n", current_cycle);
  }
  else if (USES_FP_FU(d_rs->op))
  {
    for(i=0; i<RESERV_FP_SIZE; ++i)
    {
      if (reservFP[i] == NULL) {
         reservFP[i] = d_rs;
         break;
      }
    }
    printf("INFO: dispatched a FP instruction at cycle %d\n", current_cycle);
  }
  else if (IS_UNCOND_CTRL(d_rs->op) || IS_COND_CTRL(d_rs->op))
  {
    /*
    *  unconditional & conditional branches ar enot issued to the reservation stations
    *  they do not use any FU, they do not write to the CDB
    *  they do not cause a control hazard
    */
    d_rs->tom_issue_cycle = 0;
    d_rs->tom_execute_cycle = 0;
    d_rs->tom_cdb_cycle = 0;
    printf("INFO: dispatched a branch instruction at cycle %d\n", current_cycle);
  }
  else
  {
    printf("WARNING: Unhandled instruction opcode at IFQ: %x, at cycle %d\n", d_rs->op, current_cycle);
  }
  //update map table
  d_update_mt(d_rs);

  //check for RAWs, update TAGs
  for (i = 0; i < 3; ++i)
  {
     //note: NULL value == free of RAW (i.e. tag)
     d_rs->Q[i] = map_table[d_rs->r_in[i]]->node;
  } 
  /* ECE552: Assignment 3 - END CODE */
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
  int i, reg;
  instr_lst_t *current;
  instr_lst_t *prev;

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
  /* ECE552: Assignment 3 - BEGIN CODE */
  while (true) {
     fetch_To_dispatch(trace, cycle);
     dispatch_To_issue(cycle);
     issue_To_execute(cycle);
     execute_To_CDB(cycle);
     CDB_To_retire(cycle);
     cycle++;

     if (is_simulation_done(sim_num_insn))
        break;
  }
  
  //heap clean-up
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
     if (map_table[reg] != NULL) {
       current = map_table[reg];
       do {
         prev = current;
         current = current->next;
         free(prev);
       } while (current != NULL);
     }
  }

  /* ECE552: Assignment 3 - END CODE */
  return cycle;
}
