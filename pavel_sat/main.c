#include <stdio.h>
#include <string.h>
#include <stdlib.h>

///---TYPEDEFS---
typedef struct int_list int_list;
typedef struct clause clause;
typedef struct variable variable;

//---RETURN VALUES FOR replace_watched() FUNCTION
#define VISIT_NONCHR_BACKTR -1
#define VISIT_CONFLICT 0
#define VISIT_NORMAL 1
#define VISIT_RESOLVED 2

//---DATA STRUCTURES---

struct clause {
    int size;
    int* literals;
    int watched[2];
};


struct int_list {
    int int_data;
    int_list* next;
};


struct variable {
    int assignment;
    int_list* watched[2];
    int antecedent;

    int decision_level;
    int position_in_level;
    
    int vsids;
};

//-----------------
//-----GLOBALS-----
//-----------------

//STORAGE FOR CLAUSES AND VARIABLES, PRIMARY DATA
clause* clauses = NULL;
variable* variables = NULL;
int num_variables = 0;
int num_clauses = 0;

//KEEP TRACK OF THE LEVEL'S ASSIGNMENTS TO PROPERLY BACKTRACK
int** implications = NULL;

//KEEP TRACK OF HOW MUCH VARIABLES ARE LEFT TO ASSIGN
int unassigned_count = 0;

//VSIDS GLOBALS
int decay_counter = 0;

//LIST OF CLAUSES OF SIZE ONE -> LEARNED ASSIGNMENTS
int_list* size_one_clauses = NULL;

//LIST OF CLAUSES OF SIZE ZERO -> UNSAT
int_list* size_zero_clauses = NULL;

//---DEBUGGING GLOBALS---
int num_learned = 0;
int num_branching = 0;

//------------------------
//-----END OF GLOBALS-----
//------------------------

//---FUNCTION DECLARATIONS AND SHORT IMPLEMENTATIONS---

//PARSER
int parse_cnf(const char* cnf_path);

//DPLL
int decide(int decision_level);
int assign(int variable_id, int decision_level, int assignment);
void unassign(int decision_level);

//2-LITERAL WATCHING
int replace_watched(int to_visit, int to_replace, int decision_level);

//1UIP AND NONCHRONOLOGICAL BACKTRACKING
clause* first_uip(clause* conflict_clause, int decision_level);
clause* resolve(clause* first, clause* second, int res_var);

//PREPROCESSOR
int* simplify();
int* self_subsume(int clause_id, int** occurences_pos, int** occurences_neg, int** ptr_touched);
int* subsume(int clause_id, int** occurences_pos, int** occurences_neg, int** ptr_touched);
int* maybe_eliminate(int var, int** occurences_pos, int** occurences_neg, int** ptr_touched, int** ptr_added, int** ptr_strength);
int* propagate_top_level(int** occurences_pos, int** occurences_neg, int** ptr_strength, int** ptr_touched);

//SERVICE FUNCTIONS
void attach_int_to_list(int data, int_list** attach_to);
void init_and_proceed();
void clean_up();


//This function may be used and modified for debugging purposes
void print_clause(clause* clause) {
    for (int i = 0; i < clause->size; i++) printf("%d ", clause->literals[i]);
    printf("\n");
}

FILE* open_for_solution(const char** argv) {
    FILE* output_sat;
    
    if (argv[2] == NULL) {
        char* output_filename = (malloc((strlen(argv[1]) + 1) * sizeof(char)));
        strcpy(output_filename, argv[1]);
        
        //last three characters of filename are assumed to be extension
        char* extension = output_filename + strlen(output_filename) - 3;
        extension[0] = 's';
        extension[1] = 'a';
        extension[2] = 't';
        
        extension = NULL;
        output_sat = fopen(output_filename, "w");
        free(output_filename);
    }
    
    else output_sat = fopen(argv[2], "w");
    
    return output_sat;
}


//zt_array - zero terminated array (MUST CONTAIN ZERO OR ELSE SEGMENTATION FAULT, DANGEROUS)
//the function determines position of zero in array -> array's size -> deprecated, actually, use array[0] to contain size instead
int index_of_zero(int* zt_array) {
    int index;
    for (index = 0; zt_array[index] != 0; index++);
    return index;
}

//FIND INDEX OF ELEMENT IN PORTION OF ARRAY STARTING ON start_index AND WITH SIZE width
//RETURN -1 IF NOT FOUND
int index_of_element(int element, int* array, int start_index, int width) {
    for (int i = 0; i < width; i++) if (array[i + start_index] == element) return i;
    
    return -1;
}

//RETURN NUMBER OF VARIABLES IN CLAUSE FROM CURRENT DECISION LEVEL
int num_vars_from_level(clause* clause, int decision_level) {
    int num_vars = 0;
    for (int i = 0; i < clause->size; i++) {
        if (variables[abs(clause->literals[i])].decision_level == decision_level) num_vars++;
    }
    return num_vars;
}

int is_trivial(clause* clause) {
    for (int i = 0; i < clause->size - 1; i++) {
        for (int j = i + 1; j < clause->size; j++) {
            if (clause->literals[i] == -clause->literals[j]) return 1;
        }
    }
    
    return 0;
}

//IT IS POSSIBLE THAT USING std::vector WOULD SPARE ME A LOT OF CODE, BUT SINCE THIS WAS ORIGINALLY WRITTEN IN C
//IT WOULD TAKE REALLY A LOT OF WORK TO REWRITE THIS (BUT WILL PROBABLY DO ANYWAY LATER)
int datasize(int* array) {
    return abs(array[0]);
}


//IT APPENDS ARRAY WITH AN ELEMENT AND RESIZES IT APPROPRIATELY
//THE FUNCTION EXPECTS SIZE OF THE DATA IN ARRAY ON 0'TH POSITION
int* append(int* array, int element) {
    int list_length = datasize(array);
    
    list_length++;
    int* resized = realloc(array, (list_length + 1) * sizeof(int));
    
    resized[list_length] = element;
    resized[0] = -list_length;
    return resized;

}

int* append_unique(int* array, int element) {
    if (index_of_element(element, array, 1, datasize(array)) != -1) return array;
    return append(array, element);
}

int* remove_from_list(int* array, int element) {
    
    int list_length = datasize(array);
    int remove_id = index_of_element(element, array, 1, list_length);
    
    if (remove_id == -1) return array;
    
    if (array[remove_id + 1] != element) {
        printf("remove_id + 1 = %d, element = %d\n", remove_id + 1, element);
        fprintf(stderr, "ASSERTION FAILED, WRONG ELEMENT WILL BE REMOVED\n");
        exit(1);
    }
    
    array[remove_id + 1] = array[list_length];
    array[0] = -(list_length - 1);
    array = realloc(array, list_length * sizeof(int));
    
    return array;
}

//THIS FUNCTION ADDS SET2 TO SET1, RESIZES SET1 APPROPRIATELY AND RETURNS POINTER TO NEW SET1
int* add_set_to_set(int* set1, int* set2) {
    for (int i = 1; i <= abs(set2[0]); i++) set1 = append_unique(set1, set2[i]);
    return set1;
}



//----------------
//------MAIN------
//----------------
int main(int argc, const char * argv[]) {
    
    if (argv[1] == NULL) {
        printf("usage: yasat cnf_filepath optional:solution_filepath\n");
        return 0;
    }
    
    num_clauses = parse_cnf(argv[1]);
    
    if (num_clauses == 0) {
        exit(0);
    }
    
    int need_solution = 1;
    if (argv[2] != NULL) {
        if (!strcmp(argv[2], "-s")) need_solution = 0;
    }
    
    //DO PREPROCESSING HERE
    //DEEP COPY BEFORE PREPROCESSING!
    clause* tmp_clauses = malloc(sizeof(clause) * num_clauses);
    int tmp_num_clauses = num_clauses;
    
    for (int i = 0; i < num_clauses; i++) {
        tmp_clauses[i].size = clauses[i].size;
        tmp_clauses[i].literals = malloc(sizeof(int) * tmp_clauses[i].size);
        for (int j = 0; j < tmp_clauses[i].size; j++) tmp_clauses[i].literals[j] = clauses[i].literals[j];
    }
    
    int* to_remove = simplify();
    
    if (size_zero_clauses != NULL) {
        if (need_solution) {
            FILE* output_sat = open_for_solution(argv);
            fprintf(output_sat, "s UNSATISFIABLE\n");
            fclose(output_sat);
        }
        printf("UNSATISFIABLE, TRIVIAL PROBLEM\n");
        return 0;

    }
    
    //REMOVE THOSE CLAUSES THAT SHOULD BE REMOVED
    int num_clauses_after_preprocess = 0;
    
    clause* new_clauses = malloc(sizeof(clause) * (num_clauses - datasize(to_remove)));
    for (int i = 0; i < num_clauses; i++) {
        if (index_of_element(i, to_remove, 1, datasize(to_remove)) == -1) {
            new_clauses[num_clauses_after_preprocess] = clauses[i];
            num_clauses_after_preprocess++;
        }
        else free(clauses[i].literals);
    }
    
    free(to_remove);
    to_remove = NULL;
    
    printf("number of clauses before preprocessing: %d\n", tmp_num_clauses);
    printf("number of clauses after preprocessing: %d\n", num_clauses_after_preprocess);
    
    free(clauses);
    clauses = new_clauses;
    num_clauses = num_clauses_after_preprocess;
    

    //INIT GLOBALS FOR DEBUGGING
    
    
    //TRY SETTING ALL INITIAL VALUES (SIZE-ONE CLAUSES), IF FAILS THEN UNSAT
    //IF ANY ASSIGNMENT FAILED THEN RUN THROUGH THE LIST ERASING ELEMENTS
    //IF ALL LITERALS FROM UNIT CLAUSES COUDLD BE ASSIGNED, THEN PROCEED WITH SOLVING
    
    
    init_and_proceed();
    
    int sat = decide(0);
    
    if (!need_solution) {
        if (sat) printf("SATISFIABLE\n");
        else printf("UNSATISFIABLE\n");
        clean_up();
        return 0;
    }
    
    if (sat) {
        printf("SATISFIABLE. CALCULATING ASSIGNMENT...\n");
        
        clean_up();
        
        clauses = tmp_clauses;
        num_clauses = tmp_num_clauses;
        
        init_and_proceed();
        sat = decide(0);
    }
    
    ///DEGUGGING AND OPTIMIZATION INFORMATION
    printf("clauses learned: %d\n", num_learned);
    printf("branching decisions: %d\n", num_branching);
    
    FILE* output_sat = open_for_solution(argv);
    
    if (!sat) {
        fprintf(output_sat, "s UNSATISFIABLE\n");
        printf("UNSATISFIABLE\n");
    }
    else {
        fprintf(output_sat, "s SATISFIABLE\nv ");
        for (int i = 1; i <= num_variables; i++) {
            int sign = variables[i].assignment == 0 ? -1 : 1;
            fprintf(output_sat, "%d 0\n", i * sign);
        }
        fprintf(output_sat, "0\n");
    }
    
    clean_up();
    fclose(output_sat);
}

//--------------------
//------END MAIN------
//--------------------

void init_and_proceed() {
    
    //INIT GLOBALS
    variables = (malloc(sizeof(variable) * (num_variables + 1)));
    implications = (malloc(sizeof(int*)));
    implications[0] = NULL;
    unassigned_count = num_variables;
    num_learned = 0;
    num_branching = 0;
    decay_counter = 0;
    
    //INITIALIZE ALL VARS TO DEFAULT
    for (int i = 0; i <= num_variables; i++) {
        variables[i].watched[0] = NULL;
        variables[i].watched[1] = NULL;
        variables[i].assignment = -1;
        variables[i].decision_level = -1;
        variables[i].antecedent = -1;
        variables[i].position_in_level = -1;
        variables[i].vsids = 0;
    }
    
    if (size_one_clauses != NULL) {
        fprintf(stderr, "MIGHT BE AN ISSUE, UNIT PROPAGATION NOT COMPLETE\n");
        exit(1);
    };
    
    //printf("will solve the following problem: \n");
    //DO NECESSARY INITIALIZATION FOR CLAUSES
    for (int i = 0; i < num_clauses; i++) {
        //print_clause(clauses + i);
        //IF THE CLAUSE WAS UNIT, DON'T WATCH ANYTHING, ADD TO UNIT LIST
        if (clauses[i].size == 1) {
            clauses[i].watched[0] = 0;
            clauses[i].watched[1] = 0;
            attach_int_to_list(i, &size_one_clauses);
        }
        
        //SET WATCHED LITERALS
        //ATTACH CLAUSE TO LITERAL'S APPR WATCHED LIST
        else {
            for (int watched_nr = 0; watched_nr < 2; watched_nr++) {
                clauses[i].watched[watched_nr] = clauses[i].literals[watched_nr];
                int attachID = clauses[i].literals[watched_nr];
                int p_o_n = attachID > 0 ? 0 : 1;
                attachID = abs(attachID);
                attach_int_to_list(i, &(variables[attachID].watched[p_o_n]));
            }
        }
    }
    
    implications[0] = (malloc(sizeof(int)));
    implications[0][0] = 0;
}

void clean_up() {
    
    //CLEAN UP ALL CLAUSES' LITERALS
    for (int i = 0; i < num_clauses; i++) free(clauses[i].literals);
    
    //CLEAN UP ALL VARIABLE'S WATCHED LISTS
    for (int i = 1; i <= num_variables; i++) {
        for (int p_n = 0; p_n < 2; p_n++) {
            int_list* tmp = variables[i].watched[p_n];
            while (tmp != NULL) {
                tmp = tmp->next;
                free(variables[i].watched[p_n]);
                variables[i].watched[p_n] = tmp;
            }
        }
    }
    
    //CLEAN UP EVERYTHING ELSE
    free(variables);
    free(clauses);
    free(implications);
}

//PARSER
int parse_cnf(const char* cnf_filepath) {
    
    FILE* cnf = fopen(cnf_filepath, "r");
    if (cnf == NULL){
        fprintf(stderr, "PARSE ERROR: file not found!\n");
        return 0;
    }
    num_variables = 0;
    clauses = (malloc(0));
    
    int clause_count = 0;
    
    char* line = NULL;
    size_t buf_len = 0;
    int end_of_clause = 0;
    int clause_size = 0;
    int* clause_literals = malloc(0);
    
    while (getline(&line, &buf_len, cnf) > 0) {
        const char* sep = " \n\t\r";
        
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
        
        while (word) {
            if (!strcmp(word, "0")) {
                end_of_clause = 1;
                break;
            }
            int number = atoi(word);
            if (!number) {
                free(line);
                fclose(cnf);
                fprintf(stderr, "PARSE ERROR: unexpected char!\n");
                return 0;
            }
            if (abs(number) > num_variables) num_variables = abs(number);
            clause_literals = (realloc(clause_literals, (clause_size + 1) * sizeof(int)));
            clause_literals[clause_size] = number;
            clause_size++;
            word = strtok(NULL, sep);
        }
        
        if (clause_size > 0 && end_of_clause) {
            clauses = (realloc(clauses, (clause_count + 1) * sizeof(clause)));
            clauses[clause_count].literals = clause_literals;
            clauses[clause_count].size = clause_size;
            clause_count++;
            
            clause_size = 0;
            end_of_clause = 0;
            clause_literals = malloc(0);
        }
        free(line);
        line = NULL;
        buf_len = 0;
    }
    
    free(clause_literals);
    fclose(cnf);
    return clause_count;
}

//----------------------
//-----PREPROCESSOR-----
//----------------------

//GENERAL IDEA: CREATE NEW CLAUSES TO SUBSUME OLD ONES AND EVENTUALLY GENERATE A LIST
//WITH INDICES OF CLAUSES THAT SHOULD BE REMOVED

int* simplify() {
    
    //USE THESE THREE ARRAYS TO HOLD INDICES OF VARS AND CLAUSES THAT HAVE UNDERGONE MODIFICATION
    int* to_remove = malloc(sizeof(int));
    to_remove[0] = 0;
    
    int* added = malloc(sizeof(int) * (num_clauses + 1));
    added[0] = -num_clauses;
    for (int i = 1; i <= num_clauses; i++) added[i] = i - 1;
    
    int* touched = malloc(sizeof(int) * (num_variables + 1));
    touched[0] = -num_variables;
    for (int i = 1; i <= num_variables; i++) touched[i] = i;

    int* strengthened = malloc(sizeof(int));
    strengthened[0] = 0;
    
    //ALSO NEED LIST OF OCCURENCES!
    int** occurences_pos = malloc(sizeof(int*) * (num_variables + 1));
    occurences_pos[0] = NULL;
    
    for (int i = 1; i <= num_variables; i++) {
        occurences_pos[i] = malloc(sizeof(int));
        occurences_pos[i][0] = 0;
    }
    
    int** occurences_neg = malloc(sizeof(int*) * (num_variables + 1));
    occurences_neg[0] = NULL;
    
    for (int i = 1; i <= num_variables; i++) {
        occurences_neg[i] = malloc(sizeof(int));
        occurences_neg[i][0] = 0;
    }
    
    for (int clause_id = 0; clause_id < num_clauses; clause_id++) {
        for (int j = 0; j < clauses[clause_id].size; j++) {
            int var = clauses[clause_id].literals[j];
            if (var > 0) occurences_pos[var] = append_unique(occurences_pos[var], clause_id);
            else occurences_neg[-var] = append_unique(occurences_neg[-var], clause_id);
        }
    }
    
    do {
        
        int tmp_clause = datasize(added) / 2 + 1; //choose clause sort-of randomly;
        int tmp_literal = clauses[added[tmp_clause]].literals[0];
        
        int* set0 = malloc(sizeof(int));
        set0[0] = 0;
        
        set0 = add_set_to_set(set0, tmp_literal > 0 ? occurences_pos[tmp_literal] : occurences_neg[-tmp_literal]);
        //here pick clause from added(random) and pick literal from there and let set0 be list of that literal's occurences
        
        do {
            int* set1 = malloc(sizeof(int));
            set1[0] = 0;
            tmp_clause = added[1];
            tmp_literal = clauses[tmp_clause].literals[0];
            int* appr_list = tmp_literal > 0 ? occurences_neg[tmp_literal] : occurences_pos[-tmp_literal];
            
            set1 = add_set_to_set(set1, appr_list);
            set1 = add_set_to_set(set1, added);
            set1 = add_set_to_set(set1, strengthened);
            
            free(added);
            free(strengthened);
            
            added = malloc(sizeof(int));
            added[0] = 0;
            strengthened = malloc(sizeof(int));
            strengthened[0] = 0;
            
            //will touch variables
            //this part will strengthen clauses, not generate them and not remove them (apparently)
            //so need to pass strenghened[] array to self_subsume to modify (or return generated strengthened[] array)
            //and need both occurence lists (r/w)
            //should also care about clauses that became zero (is possible, huh)
            
            //DONE (apparently)
            for (int i = 1; i <= datasize(set1); i++) {
                int* new_strengthened = self_subsume(set1[i], occurences_pos, occurences_neg, &touched);
                strengthened = add_set_to_set(strengthened, new_strengthened);
                free(new_strengthened);
                new_strengthened = NULL;
            }
            
            //propagate top_level (size-one clauses!)
            //will touch variables
            //this might remove clauses as well as strenghten them -> both to-remove and strengthened arrays will be modified by these
            //need also information about which ones have become unit
            //and of course occurences lists to modify, duh
            //thank god it doesn't generate new ones
            
            int* new_removed = propagate_top_level(occurences_pos, occurences_neg, &strengthened, &touched);
            to_remove = add_set_to_set(to_remove, new_removed);
            free(new_removed);
            new_removed = 0;
            
            free(set1);
            set1 = NULL;
            
        } while (datasize(strengthened) != 0);
        
        for (int i = 1; i <= datasize(set0); i++) {
            //will touch variables
            //this also needs [occurences] list to modify and will remove clauses -> return or modify inside
            if (index_of_element(set0[i], to_remove, 1, datasize(to_remove)) < 0) {
                int* new_removed = subsume(set0[i], occurences_pos, occurences_neg, &touched);
                to_remove = add_set_to_set(to_remove, new_removed);
                free(new_removed);
                new_removed = NULL;
            }
        }
        
        do {
            int* set = touched;
            touched = malloc(sizeof(int));
            touched[0] = 0;
            
            for (int i = 1; i < datasize(set); i++) {
                //it will generate clauses -> will modify added, but also remove clauses that are subsumed
                //and top-level propagation will strengthen some
                //top-level propagation needs info about clauses of size 1
                //need to modify occurences list
                int* new_removed = maybe_eliminate(set[i], occurences_pos, occurences_neg, &touched, &added, &strengthened);
                to_remove = add_set_to_set(to_remove, new_removed);
                free(new_removed);
                new_removed = NULL;
            }
            
            free(set);
            set = NULL;
            
        } while (datasize(touched) != 0);
        
        free(set0);
        set0 = NULL;
    } while (datasize(added) != 0);
    
    for (int i = 0; i <= num_variables; i++) {
        free(occurences_pos[i]);
        free(occurences_neg[i]);
    }
    
    free(occurences_pos);
    free(occurences_neg);
    free(added);
    free(touched);
    free(strengthened);
    
    return to_remove;
}

//might result in a problem with strengthening size-one clause leading to weird stuff
// -> don't strengthen size-one clauses -> or do but keep track of them

void strengthen(int clause_id, int literal, int** occurences_pos, int** occurences_neg, int** ptr_touched) {
    
    clause* to_strengthen = clauses + clause_id;
    printf("removed literal %d from clause ", literal);
    print_clause(clauses + clause_id);
    //TOUCH ALL VARIABLES FROM STRENGTHENED CLAUSE
    for (int j = 0; j < to_strengthen->size; j++) {
        int var = abs(to_strengthen->literals[j]);
        *ptr_touched = append_unique(*ptr_touched, var);
    }
    //if we strengthen the clause we remove the literal from there, and then remove this clause's id from
    //the occurences list of that literal
    
    //REPLACE THE LITERAL THAT SHOULD BE REMOVED WITH THE CLAUSE'S LAST LITERAL AND RESIZE APPROPRIATELY
    int remove_index = index_of_element(literal, to_strengthen->literals, 0, to_strengthen->size);
    
    if (remove_index == -1) {
        fprintf(stderr, "ASSERTION FAILED. DIDN'T FIND LITERAL TO STRENGTHEN");
        exit(1);
    }
    
    to_strengthen->literals[remove_index] = to_strengthen->literals[to_strengthen->size - 1];
    to_strengthen->size -= 1;
    
    to_strengthen->literals = realloc(to_strengthen->literals, to_strengthen->size * sizeof(int));
    
    if (to_strengthen->size == 0) attach_int_to_list(clause_id, &size_zero_clauses);
    if (to_strengthen->size == 1) attach_int_to_list(clause_id, &size_one_clauses);
    
    if (literal > 0) occurences_pos[literal] = remove_from_list(occurences_pos[literal], clause_id);
    else occurences_neg[-literal] = remove_from_list(occurences_neg[-literal], clause_id);
}

int subset (int clause_id, int candidate_id) {
    for (int i = 0; i < clauses[clause_id].size; i++) {
        if (index_of_element(clauses[clause_id].literals[i], clauses[candidate_id].literals, 0, clauses[candidate_id].size) == -1) return 0;
    }
    return 1;
}

int* find_subsumed(int clause_id, int** occurences_pos, int** occurences_neg) {
    int* all_subsumed = malloc(sizeof(int));
    all_subsumed[0] = 0;
    
    //FIND LITERAL WITH SHORTEST OCCURENCES LIST
    int least_occurs = 0;
    int sh_literal = 0;
    
    for (int i = 0; i < clauses[clause_id].size; i++) {
        int lit_cand = clauses[clause_id].literals[i];
        int* appr_list = lit_cand > 0 ? occurences_pos[lit_cand] : occurences_neg[-lit_cand];
        if (datasize(appr_list) < least_occurs || least_occurs == 0) {
            sh_literal = lit_cand;
            least_occurs = datasize(appr_list);
        }
    }
    
    int* subs_candidates = sh_literal > 0 ? occurences_pos[sh_literal] : occurences_neg[-sh_literal];
    for (int i = 1; i <= datasize(subs_candidates); i++) {
        if (subs_candidates[i] == clause_id) continue;
        if (clauses[subs_candidates[i]].size < clauses[clause_id].size) continue;
        if (!subset(clause_id, subs_candidates[i])) continue;
        
        all_subsumed = append(all_subsumed, subs_candidates[i]);
    }
    
    return all_subsumed;
}

int* self_subsume(int clause_id, int** occurences_pos, int** occurences_neg, int** ptr_touched) {
    
    int* strengthened = malloc(sizeof(int));
    strengthened[0] = 0;
    
    for (int i = 0; i < clauses[clause_id].size; i++) {
        int literal = clauses[clause_id].literals[i];
        clauses[clause_id].literals[i] = -literal;
        int* all_subsumed = find_subsumed(clause_id, occurences_pos, occurences_neg);
        clauses[clause_id].literals[i] = literal;
        
        for (int j = 1; j <= datasize(all_subsumed); j++) strengthen(all_subsumed[j], -literal, occurences_pos, occurences_neg, ptr_touched);
        strengthened = add_set_to_set(strengthened, all_subsumed);
        
        free(all_subsumed);
        all_subsumed = NULL;
    }
    return strengthened;
}

//REMOVE ANY CLAUSE SUBSUMED BY clause_id, ERASE THE REMOVED CLAUSE FROM IT'S LITERALS' OCCURENCES LIST
//REMOVING IS DONE BY RETURNING A LIST OF CLAUSES TO BE REMOVED
int* subsume(int clause_id, int** occurences_pos, int** occurences_neg, int** ptr_touched) {
    
    int* to_remove = find_subsumed(clause_id, occurences_pos, occurences_neg);
    
    for (int i = 1; i <= datasize(to_remove); i++) {
        for (int j = 0; j < clauses[to_remove[i]].size; j++) {
            
            int literal = clauses[to_remove[i]].literals[j];
            int var = abs(literal);
            
            //TOUCH VARIABLE FROM SUBSUMED CLAUSE
            *ptr_touched = append_unique(*ptr_touched, var);
            
            //REMOVE THE CLAUSE FROM IT'S LITERALS' OCCURENCES LIST
            if (literal > 0) occurences_pos[literal] = remove_from_list(occurences_pos[literal], to_remove[i]);
            else occurences_neg[-literal] = remove_from_list(occurences_neg[-literal], to_remove[i]);
        }
    }
    return to_remove;
}

//first, two sets, then resolve all clauses from one set with clauses from another set
//then check if too many extra clauses were generated - abort in this case
//then remove all clauses from these two sets, add newly created clauses to added and that's it
//also erase occurences for the var
//and for all literals from new clauses - touch
int* maybe_clause_distribute(int var, int** occurences_pos, int** occurences_neg, int** ptr_touched, int** ptr_added) {
    int* to_remove = malloc(sizeof(int));
    to_remove[0] = 0;
    
    clause* new_learned = malloc(0);
    int num_learned = 0;
    
    for (int pos = 1; pos <= datasize(occurences_pos[var]); pos++) {
        for (int neg = 1; neg <= datasize(occurences_neg[var]); neg++) {
            clause* new_clause = resolve(clauses + occurences_pos[var][pos], clauses + occurences_neg[var][neg], var);
            if (is_trivial(new_clause)) {
                free(new_clause->literals);
                free(new_clause);
                new_clause = NULL;
                continue;
            }
            new_learned = realloc(new_learned, sizeof(clause) * (num_learned + 1));
            new_learned[num_learned] = *new_clause;
            num_learned++;
            free(new_clause);
        }
    }
    
    //TOO MANY CLAUSES GENERATED, ABORT EVERYTHING
    if (num_learned > abs(occurences_pos[var][0]) + abs(occurences_neg[var][0])) {
        for (int i = 0; i < num_learned; i++) {
            free(new_learned[i].literals);
        }
        free(new_learned);
        return to_remove;
    }
    
    //ELSE
    //erase occurences for ALL the vars from erased clauses
    //touch all the vars from erased clauses
    //add clauses to to_remove list
    
    //FOR EVERY ERASED CLAUSE
    int* erased_occurences[2];
    erased_occurences[0] = malloc(sizeof(int));
    erased_occurences[0][0] = 0;
    erased_occurences[1] = malloc(sizeof(int));
    erased_occurences[1][0] = 0;
    
    erased_occurences[0] = add_set_to_set(erased_occurences[0], occurences_pos[var]);
    erased_occurences[1] = add_set_to_set(erased_occurences[1], occurences_neg[var]);
    
    for (int p_n = 0; p_n <= 1; p_n++) {
        for (int i = 1; i <= datasize(erased_occurences[p_n]); i++) {
            //FOR EVERY LITERAL OF THAT CLAUSE
            int erased_id = erased_occurences[p_n][i];
            for (int lit = 0; lit < clauses[erased_id].size; lit++) {
                int literal = clauses[erased_id].literals[lit];
                //REMOVE THE CLAUSE FROM THE LITERAL'S WATCHED LIST
                if (literal > 0) occurences_pos[literal] = remove_from_list(occurences_pos[literal], erased_id);
                else occurences_neg[-literal] = remove_from_list(occurences_neg[-literal], erased_id);
                
                //TOUCH VARIABLE
                *ptr_touched = append_unique(*ptr_touched, abs(literal));
            }
            to_remove = append_unique(to_remove, erased_id);
        }
    }
    
    free(erased_occurences[0]);
    free(erased_occurences[1]);
    
    //SECURE ENOUGH SPACE IN VAULT FOR NEW CLAUSES
    clauses = realloc(clauses, sizeof(clause) * (num_clauses + num_learned));
    
    for (int i = 0; i < num_learned; i++) {
        //FOR EVERY LITERAL OF NEW CLAUSE ADD THE CLAUSE'S ID TO OCCURENCES LIST
        for(int lit = 0; lit < new_learned[i].size; lit++) {
            int literal = new_learned[i].literals[lit];
            if (literal > 0) occurences_pos[literal] = append_unique(occurences_pos[literal], num_clauses);
            else occurences_neg[-literal] = append_unique(occurences_neg[-literal], num_clauses);
        }
        //ADD THE CLAUSE TO ADDED LIST
        *ptr_added = append_unique(*ptr_added, num_clauses);
        
        if (new_learned[i].size == 1) attach_int_to_list(num_clauses, &size_one_clauses);
        if (new_learned[i].size == 0) {
            attach_int_to_list(num_clauses, &size_zero_clauses);
        }
        
        //AND ADD NEWLY LEARNED CLAUSE TO DATABASE!
        clauses[num_clauses] = new_learned[i];
        num_clauses++;
    }
    
    free(new_learned);
    return to_remove;
}

int* maybe_eliminate(int var, int** occurences_pos, int** occurences_neg, int** ptr_touched, int** ptr_added, int** ptr_strength) {
    int* to_remove = malloc(sizeof(int));
    to_remove[0] = 0;
    
    if (occurences_pos[var][0] == 0 || occurences_neg[var][0] == 0) return to_remove;
    if (abs(occurences_pos[var][0]) > 10 && abs(occurences_neg[var][0]) > 10) return to_remove;
    
    //DON'T USE DEFINITIONS SINCE IT'S KINDA COMPLICATED
    
    //will remove clauses -> will return to_remove list
    //will modify list of occurences (append even)
    //will add clauses -> modify added
    //will touch variables -> modify touched
    //won't strengthen
    
    int* new_removed = maybe_clause_distribute(var, occurences_pos, occurences_neg, ptr_touched, ptr_added);
    to_remove = add_set_to_set(to_remove, new_removed);
    free(new_removed);
    
    //if x eliminated -> propagate top level -> strengthened!
    if (datasize(to_remove) != 0) {
        new_removed = propagate_top_level(occurences_pos, occurences_neg, ptr_strength, ptr_touched);
        to_remove = add_set_to_set(to_remove, new_removed);
        free(new_removed);
    }
    
    
    return to_remove;
}

//top-level propagation will - strengthen clauses, remove clauses - need strenghtened list
//really needs list of occurences
//will use information about clauses of size 1
int* propagate_top_level(int** occurences_pos, int** occurences_neg, int** ptr_strength, int** ptr_touched) {
    int* to_remove = malloc(sizeof(int));
    to_remove[0] = 0;
    
    //THERE IS A LIST OF CLAUSES OF SIZE ONE
    int_list* tmp = size_one_clauses;
    while (tmp != NULL) {
        
        if (clauses[tmp->int_data].size == 0) {
            tmp = tmp->next;
            free(size_one_clauses);
            size_one_clauses = tmp;
            continue;
        }
        
        int lit_assigned = clauses[tmp->int_data].literals[0];
        
        //FIRST STAGE TO REMOVE ALL THE CLAUSES WHERE THIS LITERAL ONES THE CLAUSE (INCLUDING SIZE ONE, ACTUALLY)
        // -> in this step you should also erase occurence of that clause's literals
        // -> automatically erasing list of occurences of the lit of size-one clause, hopefully
        int* oned = malloc(sizeof(int));
        oned[0] = 0;
        
        oned = add_set_to_set(oned, lit_assigned > 0 ? occurences_pos[lit_assigned] : occurences_neg[-lit_assigned]);
        
        for (int i = 1; i <= datasize(oned); i++) {
            int remove_id = oned[i];
            for (int j = 0; j < clauses[remove_id].size; j++) {
                int literal = clauses[remove_id].literals[j];
                if (literal > 0) occurences_pos[literal] = remove_from_list(occurences_pos[literal], remove_id);
                else occurences_neg[-literal] = remove_from_list(occurences_neg[-literal], remove_id);
                
                //TOUCH VARS FROM REMOVED CLAUSES, DON'T TOUCH ASSIGNED LITERAL (WILL UNTOUCH IT LATER)
                *ptr_touched = append_unique(*ptr_touched, abs(literal));
                
            }
        }
        
        free(oned);
        oned = NULL;
        
        //THEN ALL CLAUSES CONTAINING THE NEGATIVE OF LITERAL BEING IN A CLAUSE OF SIZE ONE SHOULD BE STRENGHTENED
        int* zeroed = malloc(sizeof(int));
        zeroed[0] = 0;
        
        zeroed = add_set_to_set(zeroed, lit_assigned > 0 ? occurences_neg[lit_assigned] : occurences_pos[-lit_assigned]);
        
        //REMOVE THE NEGATIVE OF INITIATOR FROM ALL THE CLAUSES IT OCCURS IN
        for (int i = 1; i <= datasize(zeroed); i++) {
            int strengthen_id = zeroed[i];
            
            strengthen(strengthen_id, -lit_assigned, occurences_pos, occurences_neg, ptr_touched);
            *ptr_strength = append_unique(*ptr_strength, strengthen_id);
        }
        
        *ptr_touched = remove_from_list(*ptr_touched, abs(lit_assigned));
        
        free(zeroed);
        zeroed = NULL;
        
        tmp = tmp->next;
        free(size_one_clauses);
        size_one_clauses = tmp;
    }
    
    return to_remove;
}

//-----------------------------
//-----END OF PREPROCESSOR-----
//-----------------------------

int decide(int decision_level) {
    
    //bottom of the problem is reached
    //clean up implications since no backtracking is necessary anymore
    if (unassigned_count == 0) {
        for (int i = 0; i < decision_level; i++) {
            free(implications[i]);
            implications[i] = NULL;
        }
        return 1;
    }
    
    //UPDATE GLOBAL IMPLICATIONS STORAGE
    implications = (realloc(implications, (decision_level + 1) * sizeof(int*)));
    
    //ON DECISION LEVEL 0 ASSIGN LITERALS FROM ONE-SIZED CLAUSES AND ASSIGNMENTS THAT WERE LEARNED AS A RESULT OF 1UIP
    //THIS IS DONE IN A LOOP THAT GOES ON UNTIL THERE ARE NO VARIABLES TO ASSIGN
    if (decision_level == 0) {
        int sat = 1;
        do {
            int_list* tmp = size_one_clauses;
            while (tmp != NULL) {
                if (sat) {
                    int to_assign = clauses[tmp->int_data].literals[0];
                    int assignID = abs(to_assign);
                    int assignment = to_assign > 0 ? 1 : 0;
                    
                    //THIS VARIABLE IS NOT ASSIGNED YET, ASSIGN
                    if (variables[assignID].assignment == -1) sat = assign(assignID, 0, assignment);
                    
                    //THIS VARIABLE ALREADY HAS SATISFYING ASSIGNMENT
                    else if (variables[assignID].assignment == assignment) sat = 1;
                    
                    //THIS VARIABLE ALREADY HAS CONFLICTING ASSIGNMENT,
                    //SINCE IT IS LEVEL 0 NO CONFLICT IS ALLOWED HERE, WHICH MEANS UNSAT PROBLEM
                    else sat = 0;
                }
                tmp = tmp->next;
                free(size_one_clauses);
                size_one_clauses = tmp;
            }
            
            //IF ALL ASSIGNMENTS SUCCESSFUL, START SOLVING
            if (sat) sat = decide(1);
        } while (size_one_clauses != NULL);
        
        return sat;
    }
    
    
    //FIND VARIABLE WITH LARGEST VSIDS TO ASSIGN
    int variable_candidate = 0;
    
    int top_vsids = -1;
    for (int i = 1; i <= num_variables; i++) {
        if (variables[i].assignment == -1 && variables[i].vsids > top_vsids) {
            top_vsids = variables[i].vsids;
            variable_candidate = i;
        }
    }
    
    int variable_id = variable_candidate;
    
    if (variables[variable_id].assignment != -1) {
        fprintf(stderr, "FAILED ASSERTION! ASSIGNING ALREADY ASSIGNED VARIABLE!\n");
        exit(1);
    }
    
    //TRY ASSIGNING, IN CASE OF SUCCESS MOVE TO THE NEXT DECISION LEVEL
    for (int assignment = 0; assignment < 2; assignment++) {
        num_branching++;
        
        implications[decision_level] = (malloc(2 * sizeof(int)));
        
        //for performance and simplicity reasons the number of implications at current level
        //is stored as a negative number at index 0 of implications array
        implications[decision_level][0] = -1;
        implications[decision_level][1] = variable_id;
        
        //TRY ASSIGNING, IF SUCCESSFUL GO TO THE NEXT LEVEL
        int success = assign(variable_id, decision_level, assignment);
        
        if (success > 0) success = decide(decision_level + 1);
        if (success > 0) return 1;
        
        //NOT SUCCESSFUL, DECIDE WHERE TO BACKTRACK
        unassign(decision_level);
        
        //BACKTRACK TO HERE, TRY THIS ASSIGNMENT AGAIN, WITH NEW CONFLICT INFO
        if (success == VISIT_NONCHR_BACKTR) {
            assignment--;
        }
        
        //BACKTRACK FURTHER
        if (success < VISIT_NONCHR_BACKTR) {
            return success + 1;
        }
    }
    
    return 0;
}

int assign(int variable_id, int decision_level, int assignment) {
    
    //ACTUALLY ASSIGN LITERAL
    variables[variable_id].assignment = assignment;
    variables[variable_id].decision_level = decision_level;
    variables[variable_id].position_in_level = abs(implications[decision_level][0]) - 1;
    unassigned_count--;
    
    //TWO POINTERS FOR TRAVERSING LIST OF CLAUSES IN WHICH THE LITERAL IS WATCHED.
    //CLAUSES, WHERE THERE WAS FOUND ANOTHER LITERAL TO WATCH SHOULD BE REMOVED FROM THE LIST
    int_list* to_update;
    int_list* crt;
    
    
    to_update = variables[variable_id].watched[assignment];
    crt = to_update;
    
    //KOCTbI/\b
    int sign = 1 - assignment * 2;
    
    while (to_update != NULL) {
        //TRY FINDING IN EACH CLAUSE ANOTHER LITERAL TO WATCH
        int result = replace_watched(to_update->int_data, variable_id * sign, decision_level);
        
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
        else if (result <= VISIT_CONFLICT) {
            return result - VISIT_CONFLICT;
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

//NECESSARY CLEAN-UP FOR BACKTRACKING IS DONE HERE
void unassign(int decision_level) {
    
    //INCREMENT VSIDS FOR VARIABLES THAT PRODUCED CONFLICT
    decay_counter++;

    //PERIODICALLY DECAY VSIDS
    if (decay_counter == 50) {
        for (int i = 1; i <= num_variables; i++) {
            variables[i].vsids /= 2;
        }
        decay_counter = 0;
    }
    
    //ERASE ASSIGNMENT
    for (int i = 1; i <= abs(implications[decision_level][0]); i++) {
        variables[implications[decision_level][i]].vsids++;
        variables[implications[decision_level][i]].assignment = -1;
        variables[implications[decision_level][i]].decision_level = -1;
        variables[implications[decision_level][i]].antecedent = -1;
        variables[implications[decision_level][i]].position_in_level = -1;
        unassigned_count++;
    }
    
    //CLEAR LIST OF THIS LEVEL ASSIGNMENTS
    free(implications[decision_level]);
    implications[decision_level] = NULL;
}

int replace_watched(int to_visit, int to_replace, int decision_level) {
    
    clause* current = clauses + to_visit;
    //find another unassigned literal to watch
    //if none, check if resolved
    //if not resolved, check if unit -> imply
    //if not impliable -> learn conflict clause -> CONFLICT backtrack
    
    //FIRST OF ALL, LOOK FOR ANOTHER LITERAL TO WATCH
    for (int i = 0; i < current->size; i++) {
        
        //SINCE CLAUSE STORES LITERALS AS ID * SIGN, ID and SIGN SHOULD BE FIRST CALCULATED
        int candidate = current->literals[i];
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
        if ((candidate_resolves || variables[candidateID].assignment < 0) && index_of_element(candidate, current->watched, 0, 2) < 0) {
            attach_int_to_list(to_visit, &(variables[candidateID].watched[watched_p_n]));
            current->watched[index_of_element(to_replace, current->watched, 0, 2)] = candidate;
            return VISIT_NORMAL;
        }
    }
    
    //NOW LET'S HAVE A LOOK AT THE OTHER WATCHED LITERAL
    //aw FOR anotherWatched
    int aw = current->watched[1 - index_of_element(to_replace, current->watched, 0, 2)];
    int aw_resolving_assignment = aw > 0 ? 1 : 0;
    int awID = abs(aw);
    
    //IF IT IS RESOLVING THIS CLAUSE THEN NO MORE WORK HERE
    if (variables[awID].assignment == aw_resolving_assignment) return VISIT_RESOLVED;
    
    //OR THERE IN AN IMPLICATION, IN CASE OF SUCCESSFUL IMPLICATION RETURN VISIT_RESOLVED
    //ELSE PROPAGATE THE CONFLICT
    
    if (variables[awID].assignment < 0) {
        //determine how many implications were already done on this (the 0th element holds negative size)
        int implications_size = abs(implications[decision_level][0]);
        
        //then resize the stuff appropriately
        implications_size++;
        implications[decision_level] = (realloc(implications[decision_level], (implications_size + 1) * sizeof(int)));
        
        //set the last implication to awID, which underwent implication
        implications[decision_level][implications_size] = awID;
        
        //then update 0th element to hold new size
        implications[decision_level][0] = -implications_size;
        
        //mark this clause as antecedent for this variable
        variables[awID].antecedent = to_visit;
        
        int implication_success = assign(awID, decision_level, aw_resolving_assignment);
        
        if (implication_success > 0) return VISIT_RESOLVED;
        else return VISIT_CONFLICT + implication_success;
    }
    
    //ANOTHER WATCH HAS ALSO ZEROING ASSIGNMENT, WHICH LEADS TO CONFLICT!
    if (decision_level == 0) return VISIT_CONFLICT;
    
    clause* learned_clause = first_uip(clauses + to_visit, decision_level);
    
    //FIND OUT SECOND LATEST DECISION LEVEL IN A LEARNED CLAUSE TO BACKTRACK TO
    //IF NOT FOUND, THEN LEARNED CLAUSE IS UNIT, RETURN TO LEVEL ZERO AND ASSIGN
    int max_exc_current = 0;
    int this_level_var = 0;
    int latest_prev_var = 0;
    
    for (int i = 0; i < learned_clause->size; i++) {
        int check_var = learned_clause->literals[i];
        int max_candidate = variables[abs(check_var)].decision_level;
        if (max_candidate > max_exc_current && max_candidate != decision_level) {
            latest_prev_var = check_var;
            max_exc_current = max_candidate;
        }
        if (max_candidate == decision_level) {
            this_level_var = check_var;
        }
    }
    
    //IT IS POSSIBLE THAT ALL VARIABLES EXCEPT FOR CURRENT LEVEL VARIABLE WERE PRE-ASSIGNED
    //IN THIS CASE WE LEARNED NEW ASSIGNMENT (GO BACK TO LEVEL 1)
    if (max_exc_current == 0 && learned_clause->size > 1) {
        learned_clause->size = 1;
        free(learned_clause->literals);
        learned_clause->literals = malloc(sizeof(int));
        learned_clause->literals[0] = this_level_var;
    }
    
    if (learned_clause->size > 9) {
        free(learned_clause->literals);
        free(learned_clause);
        return VISIT_CONFLICT;
    }
    
    int backtrack_levels = max_exc_current - decision_level;
    
    
    //ADD NEWLY LEARNED CLAUSE TO GLOBAL DATABASE
    num_learned++;
    clauses = realloc(clauses, (num_clauses + 1) * sizeof(clause));
    clauses[num_clauses] = *learned_clause;
    
    free(learned_clause);
    
    //FINISH PROPER INITIALIZING OF THE CLAUSE
    if (clauses[num_clauses].size == 1) {
        clauses[num_clauses].watched[0] = 0;
        clauses[num_clauses].watched[1] = 0;
        attach_int_to_list(num_clauses, &size_one_clauses);
    }
    else {
        int to_watch[2];
        //most recently assigned variables should be watched to effectively utilize non-chronological backtrack
        to_watch[0] = this_level_var;
        to_watch[1] = latest_prev_var;
        for (int watched_nr = 0; watched_nr < 2; watched_nr++) {
            clauses[num_clauses].watched[watched_nr] = to_watch[watched_nr];
            int attachID = to_watch[watched_nr];
            int p_o_n = attachID > 0 ? 0 : 1;
            attachID = abs(attachID);
            attach_int_to_list(num_clauses, &(variables[attachID].watched[p_o_n]));
        }
    }
    num_clauses++;
    return VISIT_NONCHR_BACKTR + backtrack_levels;
}

//LEARN CLAUSE FROM CONFLICT USING FIRST UIP ALGORITHM
//RESOLVE conflict WITH THE MOST RECENT ASSIGNED VARIABLE's ANTECEDENT
//WHILE THERE ARE MORE THAN 1 VARIABLES ASSIGNED ON THE LAST DECISION LEVEL IN CLAUSE
//CALLER RESPONCIBLE FOR MEMORY OF THE RETURNED POINTER
clause* first_uip(clause* conflict, int decision_level) {
    
    clause* learn_result = malloc(sizeof(clause));
    
    //INITIALIZE NEW CLAUSE TO USE IN FIRST UIP (EXPENDABLE, WILL BE OFTEN REALLOCATED)
    learn_result->size = conflict->size;
    learn_result->watched[0] = conflict->watched[0];
    learn_result->watched[1] = conflict->watched[1];
    learn_result->literals = malloc(sizeof(int) * conflict->size);
    for (int i = 0; i < conflict->size; i++) {
        learn_result->literals[i] = conflict->literals[i];
    }
    
    //nullify incoming clause pointer in order to not mess it up
    conflict = NULL;
    
    while (num_vars_from_level(learn_result, decision_level) > 1) {
        //FIND MOST RECENTLY ASSIGNED VARIABLE
        int most_recent = 0;
        for (int i = 0; i < learn_result->size; i++) {
            int candidate = abs(learn_result->literals[i]);
            if (variables[candidate].decision_level != decision_level) continue;
            if (most_recent == 0 || variables[candidate].position_in_level > variables[abs(most_recent)].position_in_level) most_recent = learn_result->literals[i];
        }
        //RESOLVE NEW C AND THE VARIABLE's ANTECEDENT CLAUSE
        clause* resolvent = resolve(learn_result, clauses + variables[abs(most_recent)].antecedent, most_recent);
        free(learn_result->literals);
        free(learn_result);
        learn_result = resolvent;
    }
    return learn_result;
}

//THIS FUNCTION IMPLEMENTS RESOLUTION (a + b)(a' + c) = (a + b)(a' + c)(b + c)
//AND RETURNS POINTER TO (b + c)
clause* resolve(clause* first, clause* second, int res_var) {
    clause* resolvent = malloc(sizeof(clause));
    resolvent->literals = malloc(0);
    
    int resolvent_size = 0;
    
    //ADD LITERALS FROM INITIATOR CLAUSE TO RESOLVING
    for (int i = 0; i < first->size; i++) {
        //this literal is valid to be in resolvent
        if (first->literals[i] != res_var) {
            resolvent->literals = realloc(resolvent->literals, sizeof(int) * (resolvent_size + 1));
            resolvent->literals[resolvent_size] = first->literals[i];
            resolvent_size++;
        }
    }
    //ADD LITERALS FROM SECOND CLAUSE TO RESOLVING
    for (int i = 0; i < second->size; i++) {
        if (second->literals[i] != -res_var && index_of_element(second->literals[i], resolvent->literals, 0, resolvent_size) < 0) {
            resolvent->literals = realloc(resolvent->literals, sizeof(int) * (resolvent_size + 1));
            resolvent->literals[resolvent_size] = second->literals[i];
            resolvent_size++;
        }
    }
    resolvent->size = resolvent_size;
    return resolvent;
}

//THIS FUNCTION IS USED TO CREATE AN INSTANCE OF STRUCT int_list WITH data AS IT'S int_data
//AND ATTACH IT TO A LIST, POINTED BY attach_to
void attach_int_to_list(int data, int_list** attach_to) {
    
    int_list* new_list_el = (malloc(sizeof(int_list)));
    new_list_el->int_data = data;
    new_list_el->next = NULL;
    
    //attach_to IS THE HEAD OF THE LIST
    int_list* tmp = *attach_to;
    
    //IF HEAD IS NULL MAKE NEW ELEMENT A HEAD
    if (tmp == NULL) {
        *attach_to = new_list_el;
        return;
    }
    
    //ELSE FIND TAIL AND HANG IT THERE
    while (tmp->next != NULL) {
        tmp = tmp->next;
    }
    tmp->next = new_list_el;
}
