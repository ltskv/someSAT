#include <stdio.h>
#include <string.h>
#include <stdlib.h>

///---TYPEDEFS---
typedef struct clause_list clause_list;
typedef struct clause clause;
typedef struct variable variable;

//---RETURN VALUES FOR replace_watched() FUNCTION
#define VISIT_CONFLICT 0
#define VISIT_NORMAL 1
#define VISIT_RESOLVED 2

//---DATA STRUCTURES---

struct clause {
    int size;
    int* literals;
    int watched[2];
};


struct clause_list {
    clause* clause_data;
    clause_list* next;
};


struct variable {
    int assignment;
    clause_list* watched[2];
};

//---GLOBALS---
clause* clauses = NULL;
variable* variables = NULL;
int variable_count = 0;
int** implications = NULL;

//---FUNCTION DECLARATIONS AND SHORT IMPLEMENTATIONS---
int parse_cnf(const char* cnf_path);
int decide(int variable_id, int decision_level);
int assign(int variable_id, int decision_level, int assignment);
void unassign(int decisionLevel);
int replace_watched(clause* clause, int to_replace, int decision_level);
void attach_clause(clause* clause, clause_list** attach_to);

int index_of_element(int element, int* array) {
    for (int i = 0; i < 2; i++) {
        if (array[i] == element) return i;
    }
    return -1;
}


//This function was used for debugging purposes
/*
 * void printClause(clause* clause) {
 *    for (int i = 0; i < clause->size; i++) printf("%d ", clause->literals[i]);
 *   printf("\n");
 * }
 */

//zt_array - zero terminated array (MUST BE ZERO TERMINATED)
//the function determines position of zero in array -> array's size
int index_of_zero(int* zt_array) {
    int index;
    for (index = 0; zt_array[index] != 0; index++);
    return index;
}


//----------------
//------MAIN------
//----------------
int main(int argc, const char * argv[]) {
    
    if (argv[1] == NULL) {
        printf("usage: yasat cnf_filepath\n");
        return 0;
    }
    
    int num_clauses = parse_cnf(argv[1]);
    
    if (num_clauses == 0) {
        free(clauses);
        exit(0);
    }
    
    //INIT GLOBALS
    variables = (malloc(sizeof(variable) * (variable_count + 1)));
    implications = (malloc(sizeof(int*)));
    implications[0] = NULL;
    
    //INITIALIZE ALL LITERALS TO DEFAULT
    for (int i = 0; i <= variable_count; i++) {
        variables[i].watched[0] = NULL;
        variables[i].watched[1] = NULL;
        variables[i].assignment = -1;
    }
    
    clause_list* unit = NULL;
    
    //DO NECESSARY INITIALIZATION
    for (int i = 0; i < num_clauses; i++) {
        //IF THE CLAUSE WAS UNIT, DON'T WATCH ANYTHING, USE UNUSED LITERAL 0 FOR STORING LIST OF UNIT CLAUSES
        if (clauses[i].size == 1) {
            clauses[i].watched[0] = 0;
            clauses[i].watched[1] = 0;
            attach_clause(clauses + i, &unit);
        }
        
        //SET WATCHED LITERALS
        //ATTACH CLAUSE TO LITERAL'S APPR WATCHED LIST
        else {
            for (int indexOfWatched = 0; indexOfWatched < 2; indexOfWatched++) {
                clauses[i].watched[indexOfWatched] = clauses[i].literals[indexOfWatched];
                int attachID = clauses[i].literals[indexOfWatched];
                int posOrNeg = attachID > 0 ? 0 : 1;
                attachID = abs(attachID);
                attach_clause(clauses + i,&(variables[attachID].watched[posOrNeg]));
            }
        }
    }
    
    implications[0] = (malloc(sizeof(int)));
    implications[0][0] = 0;
    
    //TRY SETTING ALL INITIAL VALUES (UNIT CLAUSES), IF FAILS THEN UNSAT
    //IF ANY ASSIGNMENT FAILED THEN RUN THROUGH THE LIST ERASING ELEMENTS
    clause_list* tmp = unit;
    int sat = 1;
    
    while (tmp != NULL) {
        if (sat) {
            int to_assign = tmp->clause_data->literals[0];
            int assignID = abs(to_assign);
            int assignment = to_assign > 0 ? 1 : 0;
            sat = assign(assignID, 0, assignment);
        }
        tmp = tmp->next;
        free(unit);
        unit = tmp;
    }
    
    //IF ALL LITERALS FROM UNIT CLAUSES COUDLD BE ASSIGNED, THEN PROCEED WITH SOLVING
    if (sat) sat = decide(1, 1);
    
    char* output_filename = (malloc((strlen(argv[1]) + 1) * sizeof(char)));
    strcpy(output_filename, argv[1]);
    
    //last three characters of filename are assumed to be extension
    char* extension = output_filename + strlen(output_filename) - 3;
    extension[0] = 's';
    extension[1] = 'a';
    extension[2] = 't';
    
    extension = NULL;
    
    FILE* output_cnf = fopen(output_filename, "w");
    free(output_filename);
    
    
    if (!sat) fprintf(output_cnf, "s UNSATISFIABLE\n");
    else {
        fprintf(output_cnf, "s SATISFIABLE\nv ");
        for (int i = 1; i <= variable_count; i++) {
            int sign = variables[i].assignment == 0 ? -1 : 1;
            fprintf(output_cnf, "%d ", i * sign);
        }
        fprintf(output_cnf, "0\n");
    }
    
    fclose(output_cnf);
    free(clauses);
    free(variables);
    free(implications);
}

//--------------------
//------END MAIN------
//--------------------

int parse_cnf(const char* cnf_filepath) {
    
    FILE* cnf = fopen(cnf_filepath, "r");
    variable_count = 0;
    clauses = (malloc(0));
    
    int clause_count = 0;
    
    char* line = NULL;
    size_t buf_len = 0;
    
    while (getline(&line, &buf_len, cnf) > 0) {
        const char* sep = " \n\t";
        char* word = strtok(line, sep);
        if (word == NULL) {
            free(line);
            line = NULL;
            buf_len = 0;
            continue;
        }
        else if (word[0] == 'p' || word[0] == 'c') {
            free(line);
            line = NULL;
            buf_len = 0;
            continue;
        }
        clauses = (realloc(clauses, (clause_count + 1) * sizeof(clause)));
        int clause_size = 0;
        clauses[clause_count].literals = (malloc(0));
        
        while (word) {
            if (!strcmp(word, "0")) break;
            int number = atoi(word);
            if (!number) {
                free(line);
                fclose(cnf);
                fprintf(stderr, "PARSE ERROR: unexpected char!\n");
                return 0;
            }
            if (abs(number) > variable_count) variable_count = abs(number);
            clauses[clause_count].literals = (realloc(clauses[clause_count].literals, (clause_size + 1) * sizeof(int)));
            clauses[clause_count].literals[clause_size] = number;
            clause_size++;
            word = strtok(NULL, sep);
        }
        clauses[clause_count].size = clause_size;
        clause_count++;
        
        free(line);
        line = NULL;
        buf_len = 0;
    }
    
    fclose(cnf);
    return clause_count;
}

//assignment 1 -> process clauses with -lit
//assignment 0 -> process clauses with lit
//1 -> -1
//0 -> 1
// 1 - 2 * assignment

int decide(int variable_id, int decision_level) {
    
    //bottom of the problem is reached
    //clean up implications since no backtracking is necessary anymore
    if (variable_id > variable_count) {
        for (int i = 0; i < decision_level; i++) {
            free(implications[i]);
            implications[i] = NULL;
        }
        return 1;
    }
    
    //this literal is already assigned, move decision to the next one
    if (variables[variable_id].assignment >= 0) return decide(variable_id + 1, decision_level);
    
    //UPDATE GLOBAL IMPLICATIONS STORAGE
    implications = (realloc(implications, (decision_level + 1) * sizeof(int*)));
    
    //TRY ASSIGNING, IN CASE OF SUCCESS MOVE TO THE NEXT DECISION LEVEL
    for (int assignment = 0; assignment < 2; assignment++) {
        
        implications[decision_level] = (malloc(2 * sizeof(int)));
        implications[decision_level][0] = variable_id;
        implications[decision_level][1] = 0;
        
        int success = assign(variable_id, decision_level, assignment);
        if (success) {
            success = decide(variable_id + 1, decision_level + 1);
        }
        if (success) return 1;
        
        unassign(decision_level);    //THIS DOES BACKTRACKING
    }
    
    return 0;
}

//literalID: literal being processed
//decisionLevel: (nuff said)
//assignment: the corresponding decision/implication
int assign(int variable_id, int decision_level, int assignment) {
    
    //ACTUALLY ASSIGN LITERAL
    variables[variable_id].assignment = assignment;
    
    //TWO POINTERS FOR TRAVERSING LIST OF CLAUSES IN WHICH THE LITERAL IS WATCHED.
    //CLAUSES, WHERE THERE WAS FOUND ANOTHER LITERAL TO WATCH SHOULD BE REMOVED FROM THE LIST
    clause_list* to_update;
    clause_list* crt;
    
    
    to_update = variables[variable_id].watched[assignment];
    crt = to_update;
    
    //KOCTbI/\b
    int sign = 1 - assignment * 2;
    
    while (to_update != NULL) {
        
        //TRY FINDING IN EACH CLAUSE ANOTHER LITERAL TO WATCH
        int result = replace_watched(to_update->clause_data, variable_id * sign, decision_level);
        
        //IF JUST FOUND
        if (result == VISIT_NORMAL){
            //IF THIS WAS THE FIRST CLAUSE ON THE LIST, MOVE LITERAL'S watched[x] POINTER TO THE NEXT, AND FREE THIS ONE
            if (to_update == variables[variable_id].watched[assignment]) {
                variables[variable_id].watched[assignment] = to_update->next;
                to_update = to_update->next;
                free(crt);
                crt = to_update;
            }
            //OTHERWISE REATTACH THE ->NEXT POINTER OF THE LAST PROCESSED CLAUSE THAT WAS KEPT ON THE LIST
            //TO THE NEXT CLAUSE TO BE PROCESSED, AND ERASE THE ALREADY PROCESSED ONE, AND INCREMENT
            else {
                crt->next = to_update->next;
                free(to_update);
                to_update = crt->next;
            }
        }
        
        //IN CASE OF CONFLICT JUST STOP AND BACKTRACK (BACKTRACKING DONE IN decide())
        else if (result == VISIT_CONFLICT) {
            return 0;
        }
        //IF THE LITERAL COULD'NT BE REPLACED, THEN CURRENT CLAUSE WAS KEPT ON THE LIST, MOVE crt POINTER TO THIS ONE
        //AND INCREMENT toUpdate
        else {
            crt = to_update;
            to_update = to_update->next;
        }
    }
    
    //SUCCESS!
    return 1;
}

void unassign(int decision_level) {
    for (int i = 0; i < index_of_zero(implications[decision_level]); i++) {
        variables[implications[decision_level][i]].assignment = -1;
    }
    free(implications[decision_level]);
    implications[decision_level] = NULL;
    
}

//toReplace: literal being replaced as watched, contains information whether watched pos or neg
int replace_watched(clause* clause, int to_replace, int decision_level) {
    
    //find another unassigned literal to watch
    //if none, check if resolved
    //if not resolved, check if unit -> imply
    //if not impliable -> CONFLICT backtrack
    
    //FIRST OF ALL, LOOK FOR ANOTHER LITERAL TO WATCH
    for (int i = 0; i < clause->size; i++) {
        
        //SINCE CLAUSE STORES LITERALS AS ID * SIGN, ID and SIGN SHOULD BE FIRST CALCULATED
        int candidate = clause->literals[i];
        int candidateID = abs(candidate);
        
        //watched positive or negarive
        int watched_p_n = candidate > 0 ? 0 : 1;
        int candidate_resolves = 0;
        
        //TRY TO DETERMINE IF WE CAN USE CANDIDATE AS ANOTHER WATCHED BECAUSE IT RESOLVES THE CLAUSE
        if (variables[candidateID].assignment >= 0) {
            candidate_resolves = (variables[candidateID].assignment - watched_p_n) == 0 ? 0 : 1;
        }
        
        //IF IT EITHER RESOLVES OR UNASSIGNED AND NOT ANOTHER WATCHED LITERAL, THEN WAS THE NORMAL CASE
        //AND WE FOUND OUR LITERAL TO WATCH
        if ((candidate_resolves || variables[candidateID].assignment < 0) && index_of_element(candidate, clause->watched) < 0) {
            attach_clause(clause, &(variables[candidateID].watched[watched_p_n]));
            clause->watched[index_of_element(to_replace, clause->watched)] = candidate;
            return VISIT_NORMAL;
        }
    }
    
    //NOW LET'S HAVE A LOOK AT THE OTHER WATCHED LITERAL
    //aw FOR anotherWatched
    int aw = clause->watched[1 - index_of_element(to_replace, clause->watched)];
    int aw_resolving_assignment = aw > 0 ? 1 : 0;
    int awID = abs(aw);
    
    //HERE COMES THE IMPLICATION
    if (variables[awID].assignment < 0) {
        //determine how many implications were already done on this level (0 marks the end)
        int implications_size = index_of_zero(implications[decision_level]);
        
        //set the last implication to awID, which underwent implication
        implications[decision_level][implications_size] = awID;
        
        //then resize the stuff appropriately and mark the end with zero
        implications_size++;
        implications[decision_level] = (realloc(implications[decision_level], (implications_size + 1) * sizeof(int)));
        implications[decision_level][implications_size] = 0;
        
        if (!assign(awID, decision_level, aw_resolving_assignment)) return VISIT_CONFLICT;
    }
    
    if (variables[awID].assignment == aw_resolving_assignment) {
        return VISIT_RESOLVED;
    }
    
    return VISIT_CONFLICT;
}

//variable_id: variable to attache clause to
//posOrNeg: whether to attach to watched pos or neg, 0 for pos, 1 for neg
void attach_clause(clause* clause, clause_list** attach_to) {
    
    clause_list* new_list_el = (malloc(sizeof(clause_list)));
    new_list_el->clause_data = clause;
    new_list_el->next = NULL;
    
    clause_list* tmp = *attach_to;
    
    if (tmp == NULL) {
        *attach_to = new_list_el;
        return;
    }
    
    while (tmp->next != NULL) {
        tmp = tmp->next;
    }
    tmp->next = new_list_el;
}
