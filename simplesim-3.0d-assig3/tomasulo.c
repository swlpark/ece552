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
static int fetch_index = 1;

//The map table keeps track of which instruction produces the value for each register
static instruction_t * map_table[MD_TOTAL_REGS];

//prints a single instruction
static void print_check_instr(instruction_t* instr) {

  md_print_insn(instr->inst, instr->pc, stdout);
  if (USES_INT_FU(instr->op) || USES_FP_FU(instr->op)) {
    assert(instr->tom_dispatch_cycle > 0 && instr->tom_dispatch_cycle == (instr->tom_issue_cycle -1) && 
    instr->tom_dispatch_cycle < instr->tom_execute_cycle && instr->tom_dispatch_cycle < instr->tom_cdb_cycle);
    assert(instr->tom_cdb_cycle == (instr->tom_execute_cycle + 4) 
        || instr->tom_cdb_cycle == (instr->tom_execute_cycle + 5)
        || instr->tom_cdb_cycle == (instr->tom_execute_cycle + 6)
        || instr->tom_cdb_cycle == (instr->tom_execute_cycle + 9)
        || instr->tom_cdb_cycle == (instr->tom_execute_cycle + 10)
        || instr->tom_cdb_cycle == (instr->tom_execute_cycle + 11));
  }
  myfprintf(stdout, "\t%d\t%d\t%d\t%d\n", 
	    instr->tom_dispatch_cycle,
	    instr->tom_issue_cycle,
	    instr->tom_execute_cycle,
	    instr->tom_cdb_cycle);
}

//prints all the instructions inside the given trace for pipeline
void check_all(instruction_trace_t* trace, int sim_num_insn) {

  fprintf(stdout, "TOMASULO TABLE\n");

  int printed_count = 0;
  int index = 1;
  while (true) {
 
     if (1) { // if (printed_count > 9999900) {
        print_check_instr(&trace->table[index]);
     }
     printed_count++;
     if (printed_count == sim_num_insn)
        break;
     if (++index == INSTR_TRACE_SIZE) {
        trace = trace->next;
	index = 0;
	if (trace == NULL)
	   break;
     }
   }
}

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
  int i;
  bool retval = false;
  bool clear = true;
  if (fetch_index > sim_insn)
  {
    for (i=0; i<RESERV_INT_SIZE; i=i+1) {
      if (reservINT[i] != NULL)
         clear = false;
    }
    for (i=0; i<RESERV_FP_SIZE; i=i+1) {
      if (reservFP[i] != NULL)
         clear = false;
    }
    retval = clear;
  }
  return retval;
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
  instruction_t * r_instr = NULL;

  //free the RS, MapTable of the entry on CDB
  for (i=0; i<RESERV_INT_SIZE; i=i+1) {
     if (reservINT[i] != NULL && reservINT[i]->tom_cdb_cycle == current_cycle) {
       if(!IS_STORE(reservINT[i]->op)) {
         r_instr = reservINT[i];
         if (map_table[r_instr->r_out[0]] == r_instr)
            map_table[r_instr->r_out[0]] = NULL;
         if (map_table[r_instr->r_out[1]] == r_instr)
            map_table[r_instr->r_out[1]] = NULL;
       }
       assert(r_instr == commonDataBus || IS_STORE(reservINT[i]->op));
       //if(IS_STORE(r_instr->op)) r_instr = NULL;
       //printf("INFO: CLEANUP an INT RS#%d at cycle %d\n", i, current_cycle);
       //print_instr(commonDataBus);
       reservINT[i] = NULL;
     }
  }
  for (i=0; i<RESERV_FP_SIZE; i=i+1) {
     if (reservFP[i] != NULL && reservFP[i]->tom_cdb_cycle == current_cycle) {
       if(!IS_STORE(reservFP[i]->op)) {
         r_instr = reservFP[i];
         if (map_table[r_instr->r_out[0]] == r_instr)
            map_table[r_instr->r_out[0]] = NULL;
         if (map_table[r_instr->r_out[1]] == r_instr)
            map_table[r_instr->r_out[1]] = NULL;
       }
       assert(r_instr == commonDataBus || IS_STORE(reservFP[i]->op));
       //if(IS_STORE(r_instr->op)) r_instr = NULL;
       //printf("INFO: CLEANUP a FP RS#%d at cycle %d\n",i, current_cycle);
       //print_instr(commonDataBus);
       reservFP[i] = NULL;
     }
  }
  if(r_instr == NULL)
    return;

  //clear matching TAGS in RS entries
  for (i=0; i<RESERV_INT_SIZE; i=i+1) {
    if (reservINT[i] != NULL && reservINT[i]->Q[0] == r_instr)
       reservINT[i]->Q[0] = NULL;
    if (reservINT[i] != NULL && reservINT[i]->Q[1] == r_instr)
       reservINT[i]->Q[1] = NULL;
    if (reservINT[i] != NULL && reservINT[i]->Q[2] == r_instr)
       reservINT[i]->Q[2] = NULL;
  }
  for (i=0; i<RESERV_FP_SIZE; i=i+1) {
    if (reservFP[i] != NULL && reservFP[i]->Q[0] == r_instr)
       reservFP[i]->Q[0] = NULL;
    if (reservFP[i] != NULL && reservFP[i]->Q[1] == r_instr)
       reservFP[i]->Q[1] = NULL;
    if (reservFP[i] != NULL && reservFP[i]->Q[2] == r_instr)
       reservFP[i]->Q[2] = NULL;
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

  //CDB instruction <= resource contention
  instruction_t * c_instr = NULL;
  commonDataBus = NULL;

  for(i=0; i<FU_INT_SIZE; i=i+1)
  {
    if (fuINT[i] != NULL && fuINT[i]->tom_execute_cycle > 0) {
       cdb_cycle = fuINT[i]->tom_execute_cycle + 4;
       if(cdb_cycle <= current_cycle) {
         if(IS_STORE(fuINT[i]->op)) {
           fuINT[i]->tom_cdb_cycle = current_cycle; 
           fuINT[i] = NULL;
         } else if(c_instr == NULL) {
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
         if(IS_STORE(fuFP[i]->op)) {
           fuFP[i]->tom_cdb_cycle = current_cycle; 
           fuFP[i] = NULL;
         } else if(c_instr == NULL) {
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

  commonDataBus = c_instr;
  if (commonDataBus == NULL)
    return;
  commonDataBus->tom_cdb_cycle = current_cycle; 
  //printf("INFO: Writeback an instruction at cycle %d\n", current_cycle);
  //print_instr(commonDataBus);


  //clear FU, RS of the completed instruction
  if (fp_fu) {
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
  int i, j; 
  instruction_t * e_instr = NULL;
  instruction_t * tmp = NULL;

  //check for an available INT FU
  for(i=0; i<FU_INT_SIZE; i=i+1)
  {
    if (fuINT[i] == NULL)
    {
       e_instr = NULL; 
       //select the oldest instruction in RS tables that is ready to exec.
       for(j=0; j<RESERV_INT_SIZE; j=j+1)
       {
          tmp = reservINT[j];
          //NULL & RAW check -- continue if a tag is not NULL
          if(tmp == NULL || tmp->Q[0] != NULL || tmp->Q[1] != NULL || tmp->Q[2] != NULL)
            continue;
          assert(tmp->tom_dispatch_cycle > 0);

          //select not yet executed RS entry, but issued 
          if (tmp->tom_execute_cycle == 0 && tmp->tom_issue_cycle > 1 &&
              tmp->tom_issue_cycle < current_cycle) {
             if (e_instr == NULL)
               e_instr = tmp; 
             else if (tmp->tom_dispatch_cycle < e_instr->tom_dispatch_cycle)
               e_instr = tmp; 
          }
       }
       if(e_instr == NULL)
         break;
       e_instr->tom_execute_cycle = current_cycle;
       fuINT[i] = e_instr;

       //printf("INFO: executed an INT instruction at cycle %d\n", current_cycle);
       //print_instr(e_instr);
    }
  }

  //check for an available FP FU
  for(i=0; i<FU_FP_SIZE; i=i+1)
  {
    if (fuFP[i] == NULL)
    {
       e_instr = NULL; 
       for(j=0; j<RESERV_FP_SIZE; j=j+1)
       {
          tmp = reservFP[j];
          //NULL & RAW check -- continue if a tag is not NULL
          if(tmp == NULL || tmp->Q[0] != NULL || tmp->Q[1] != NULL || tmp->Q[2] != NULL)
            continue;
          assert(tmp->tom_dispatch_cycle > 0);

          //select not yet executed RS entry, but issued 
          if (tmp->tom_execute_cycle == 0 && tmp->tom_issue_cycle > 1 &&
              tmp->tom_issue_cycle < current_cycle) {
             if(e_instr == NULL)
               e_instr = tmp; 
             else if (tmp->tom_dispatch_cycle < e_instr->tom_dispatch_cycle)
               e_instr = tmp; 
          }
       }
       if(e_instr == NULL)
         continue;
       e_instr->tom_execute_cycle = current_cycle;
       fuFP[i] = e_instr;

       //printf("INFO: issued a FP instruction at cycle %d\n", current_cycle);
       //print_instr(e_instr);
    }
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
  int i;
  bool issued = false;

  for(i=0; i<RESERV_INT_SIZE; i=i+1)
  {
    if (reservINT[i] != NULL && reservINT[i]->tom_issue_cycle == 0  &&
       reservINT[i]->tom_dispatch_cycle == (current_cycle - 1)) {
       assert(current_cycle >= 2);
       assert(!issued);
       reservINT[i]->tom_issue_cycle = current_cycle;
       //printf("INFO: issued an INT instruction at cycle %d\n", current_cycle);
       //print_instr(reservINT[i]);
       issued = true;
    }
  }
  for(i=0; i<RESERV_FP_SIZE; i=i+1)
  {
    if (reservFP[i] != NULL && reservFP[i]->tom_issue_cycle == 0  &&
        reservFP[i]->tom_dispatch_cycle == (current_cycle - 1)) {
       assert(current_cycle >= 2);
       assert(!issued);
       reservFP[i]->tom_issue_cycle = current_cycle;
       //printf("INFO: issued a FP instruction at cycle %d\n", current_cycle);
       //print_instr(reservFP[i]);
       issued = true;
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
static bool end = false;
void fetch(instruction_trace_t* trace) {
  /* ECE552: Assignment 3 - BEGIN CODE */
  instruction_t * f_instr;

  //fetch_index == 0 at start
  //if (fetch_index >= sim_num_insn)
  if (fetch_index > sim_num_insn)
  {
    if(!end)
      printf("INFO: reached the end of instruction trace execution ...\n");
    end = true;
    return;
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
  //update MAP table
  if (d_instr->r_out[0] != DNA)
  {
     map_table[d_instr->r_out[0]] = d_instr;
  } 
  if (d_instr->r_out[1] != DNA)
  {
     map_table[d_instr->r_out[1]] = d_instr;
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
  if (instr_queue_size == 0) {
    assert(end);
    return;
  }
  assert(instr_queue_size > 0 && instr_queue_size <= INSTR_QUEUE_SIZE);

  d_rs = instr_queue[instr_queue_tail]; 

  d_rs->tom_dispatch_cycle = 0;
  d_rs->tom_issue_cycle = 0;
  d_rs->tom_execute_cycle = 0;
  d_rs->tom_cdb_cycle = 0;

  if (USES_INT_FU(d_rs->op))
  {
    for(i=0; i<RESERV_INT_SIZE; ++i)
    {
      if (reservINT[i] == NULL) {
         d_rs->tom_dispatch_cycle = current_cycle;
         //printf("INFO: dispatched an INT instruction to INT RS #%d at cycle %d\n", i, current_cycle);
         reservINT[i] = d_rs;
         //check for RAWs, update TAGs
         for (i = 0; i < 3; ++i)
         {
            //note: NULL value == free of RAW (i.e. tag)
            d_rs->Q[i] = map_table[d_rs->r_in[i]];
         } 
         //update map table
         d_update_mt(d_rs);
        break;
      }
    }
  }
  else if (USES_FP_FU(d_rs->op))
  {
    for(i=0; i<RESERV_FP_SIZE; ++i)
    {
      if (reservFP[i] == NULL) {
         d_rs->tom_dispatch_cycle = current_cycle;
         //printf("INFO: dispatched a FP instruction to FP RS #%d at cycle %d\n", i, current_cycle);
         reservFP[i] = d_rs;
         //check for RAWs, update TAGs
         for (i = 0; i < 3; ++i)
         {
            //note: NULL value == free of RAW (i.e. tag)
            d_rs->Q[i] = map_table[d_rs->r_in[i]];
         } 
         //update map table
         d_update_mt(d_rs);
         break;
      }
    }
  }
  else if (IS_UNCOND_CTRL(d_rs->op) || IS_COND_CTRL(d_rs->op))
  {
    d_rs->tom_dispatch_cycle = current_cycle;
    //printf("INFO: dispatched a branch instruction at cycle %d\n", current_cycle);
    /*
    *  unconditional & conditional branches ar enot issued to the reservation stations
    *  they do not use any FU, they do not write to the CDB
    *  they do not cause a control hazard
    */
  }
  else
  {
    d_rs->tom_dispatch_cycle = current_cycle;
    //printf("WARNING: Unhandled instruction opcode at IFQ: %x, at cycle %d\n", d_rs->op, current_cycle);
  }

  //skip update if a RS was not found
  if (d_rs->tom_dispatch_cycle == 0)
    return;
  //print_instr(d_rs);


  //IFQ tail ptr update
  ++instr_queue_tail;
  if (instr_queue_tail == INSTR_QUEUE_SIZE)
     instr_queue_tail = 0;
  --instr_queue_size;

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

     if (is_simulation_done(sim_num_insn)) {
        check_all(trace, 1000000); 
        break;
     }
  }
  
  /* ECE552: Assignment 3 - END CODE */
  return cycle;
}
