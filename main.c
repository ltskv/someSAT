#include <stdio.h>
#include <string.h>
#include <stdlib.h>

// --- TYPEDEFS ---
typedef struct int_list int_list;
typedef struct clause clause;
typedef struct variable variable;

// --- RETURN VALUES FOR replace_watched() FUNCTION ---
#define VISIT_NONCHR_BACKTR -1
#define VISIT_CONFLICT 0
#define VISIT_NORMAL 1
#define VISIT_RESOLVED 2

// --- DATA STRUCTURES ---

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

// -----------------
// -----GLOBALS-----
// -----------------

// STORAGE FOR CLAUSES AND VARIABLES, PRIMARY DATA
clause* clauses = NULL;
variable* variables = NULL;
int num_variables = 0;
int num_clauses = 0;

// KEEP TRACK OF THE LEVEL'S ASSIGNMENTS TO PROPERLY BACKTRACK
int** implications = NULL;

// KEEP TRACK OF HOW MUCH VARIABLES ARE LEFT TO ASSIGN
int unassigned_count = 0;

// VSIDS GLOBALS
int decay_counter = 0;

// LIST OF CLAUSES OF SIZE ONE -> LEARNED ASSIGNMENTS
int_list* size_one_clauses = NULL;

// ---DEBUGGING GLOBALS--
int num_learned = 0;
int num_branching = 0;

// ------------------------
// -----END OF GLOBALS-----
// ------------------------

// ---FUNCTION DECLARATIONS AND SHORT IMPLEMENTATIONS---
int parse_cnf(const char* cnf_path);
int decide(int decision_level);
int assign(int variable_id, int decision_level, int assignment);
void unassign(int decision_level);
int replace_watched(int to_visit, int to_replace, int decision_level);
clause* first_uip(clause* conflict_clause, int decision_level);
clause* resolve(clause* conflict, clause* antecedent, int res_var);
void attach_int_to_list(int data, int_list** attach_to);



// This function may be used for debugging purposes
void print_clause(clause* clause) {
    for (int i = 0; i < clause->size; i++) {
        printf("|v%d:a%d:p%d@%d ",
                clause->literals[i],
                variables[abs(clause->literals[i])].assignment,
                variables[abs(clause->literals[i])].antecedent,
                variables[abs(clause->literals[i])].decision_level);
    }
    printf("\n");
}


// zt_array - zero terminated array
// (MUST BE ZERO TERMINATED OR ELSE SEGMENTATION FAULT)
// the function determines position of zero in array -> array's size
int index_of_zero(int* zt_array) {
    int index;
    for (index = 0; zt_array[index] != 0; index++);
    return index;
}

// FIND INDEX OF ELEMENT IN PORTION OF ARRAY STARTING ON start_index
// AND WITH SIZE width
// RETURN -1 IF NOT FOUND
int index_of_element(int element, int* array, int start_index, int width) {
    for (int i = 0; i < width; i++) {
        if (array[i + start_index] == element) return i;
    }
    return -1;
}

// RETURN NUMBER OF VARIABLES IN CLAUSE FROM CURRENT DECISION LEVEL
int num_vars_from_level (clause* c, int decision_lvl) {
    int num_vars = 0;
    for (int i = 0; i < c->size; i++) {
        if (variables[abs(c->literals[i])].decision_level == decision_lvl) {
            num_vars++;
        }
    }
    return num_vars;
}


// ----------------
// ------MAIN------
// ----------------
int main(int argc, const char * argv[]) {

    if (argv[1] == NULL) {
        printf("usage: somesat cnf_filepath [solution_filepath]\n");
        return 0;
    }

    num_clauses = parse_cnf(argv[1]);

    if (num_clauses == 0) {
        free(clauses);
        exit(0);
    }

    // INIT GLOBALS
    variables = (malloc(sizeof(variable) * (num_variables + 1)));
    implications = (malloc(sizeof(int*)));
    implications[0] = NULL;
    unassigned_count = num_variables;

    // INIT GLOBALS FOR DEBUGGING


    // INITIALIZE ALL LITERALS TO DEFAULT
    for (int i = 0; i <= num_variables; i++) {
        variables[i].watched[0] = NULL;
        variables[i].watched[1] = NULL;
        variables[i].assignment = -1;
        variables[i].decision_level = -1;
        variables[i].antecedent = -1;
        variables[i].position_in_level = -1;
        variables[i].vsids = 0;
    }

    size_one_clauses = NULL;

    // DO NECESSARY INITIALIZATION
    for (int i = 0; i < num_clauses; i++) {
        // IF THE CLAUSE WAS UNIT, DON'T WATCH ANYTHING, ADD TO UNIT LIST
        if (clauses[i].size == 1) {
            clauses[i].watched[0] = 0;
            clauses[i].watched[1] = 0;
            attach_int_to_list(i, &size_one_clauses);
        }

        // SET WATCHED LITERALS
        // ATTACH CLAUSE TO LITERAL'S APPR WATCHED LIST
        else {
            for (int watch_nr = 0; watch_nr < 2; watch_nr++) {
                clauses[i].watched[watch_nr] = clauses[i].literals[watch_nr];
                int attachID = clauses[i].literals[watch_nr];
                int pos_neg = attachID > 0 ? 0 : 1;
                attachID = abs(attachID);
                attach_int_to_list(i, &(variables[attachID].watched[pos_neg]));
            }
        }
    }

    implications[0] = (malloc(sizeof(int)));
    implications[0][0] = 0;

    // TRY SETTING ALL INITIAL VALUES (UNIT CLAUSES), IF FAILS THEN UNSAT
    // IF ANY ASSIGNMENT FAILED THEN RUN THROUGH THE LIST ERASING ELEMENTS
    // IF ALL LITERALS FROM UNIT CLAUSES COUDLD BE ASSIGNED, THEN PROCEED
    // WITH SOLVING
    int sat = decide(0);

    // /DEGUGGING AND OPTIMIZATION INFORMATION
    printf("clauses learned: %d\n", num_learned);
    printf("branching decisions: %d\n", num_branching);

    FILE* output_sat;

    if (argv[2] == NULL) {
        char* output_filename = (malloc((strlen(argv[1]) + 1) * sizeof(char)));
        strcpy(output_filename, argv[1]);

        // last three characters of filename are assumed to be extension
        char* extension = output_filename + strlen(output_filename) - 3;
        extension[0] = 's';
        extension[1] = 'a';
        extension[2] = 't';

        extension = NULL;
        output_sat = fopen(output_filename, "w");
        free(output_filename);
    }

    else output_sat = fopen(argv[2], "w");

    if (!sat) {
        fprintf(output_sat, "s UNSATISFIABLE\n");
        printf("UNSATISFIABLE\n");
    }
    else {
        printf("SATISFIABLE\n");
        fprintf(output_sat, "s SATISFIABLE\nv ");
        for (int i = 1; i <= num_variables; i++) {
            int sign = variables[i].assignment == 0 ? -1 : 1;
            fprintf(output_sat, "%d ", i * sign);
        }
        fprintf(output_sat, "0\n");
    }

    fclose(output_sat);
    free(clauses);
    free(variables);
    free(implications);
}

// --------------------
// ------END MAIN------
// --------------------

// PARSER
int parse_cnf(const char* cnf_filepath) {

    FILE* cnf = fopen(cnf_filepath, "r");
    if (cnf == NULL){
        fprintf(stderr, "PARSE ERROR: file not found: %s\n",
                cnf_filepath);
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
            clause_literals = realloc(clause_literals,
                    (clause_size + 1) * sizeof(int));
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

    fclose(cnf);
    return clause_count;
}

int decide(int decision_level) {

    // bottom of the problem is reached
    // clean up implications since no backtracking is necessary anymore
    if (unassigned_count == 0) {
        for (int i = 0; i < decision_level; i++) {
            free(implications[i]);
            implications[i] = NULL;
        }
        return 1;
    }

    // UPDATE GLOBAL IMPLICATIONS STORAGE
    implications = (realloc(implications, (decision_level + 1) * sizeof(int*)));

    // ON DECISION LEVEL 0 ASSIGN LITERALS FROM ONE-SIZED CLAUSES
    // AND ASSIGNMENTS THAT WERE LEARNED AS A RESULT OF 1UIP
    // THIS IS DONE IN A LOOP THAT GOES ON UNTIL
    // THERE ARE NO VARIABLES TO ASSIGN
    if (decision_level == 0) {
        int sat = 1;
        do {
            int_list* tmp = size_one_clauses;
            while (tmp != NULL) {
                if (sat) {
                    int to_assign = clauses[tmp->int_data].literals[0];
                    int assignID = abs(to_assign);
                    int assignment = to_assign > 0 ? 1 : 0;

                    // THIS VARIABLE IS NOT ASSIGNED YET, ASSIGN
                    if (variables[assignID].assignment == -1) {
                        sat = assign(assignID, 0, assignment);
                    }

                    // THIS VARIABLE ALREADY HAS SATISFYING ASSIGNMENT
                    else if (variables[assignID].assignment == assignment) {
                        sat = 1;
                    }
                    // THIS VARIABLE ALREADY HAS CONFLICTING ASSIGNMENT,
                    // SINCE IT IS LEVEL 0 NO CONFLICT IS ALLOWED HERE,
                    // WHICH MEANS UNSAT PROBLEM
                    else sat = 0;
                }
                tmp = tmp->next;
                free(size_one_clauses);
                size_one_clauses = tmp;
            }
            // IF ALL ASSIGNMENTS SUCCESSFUL, START SOLVING
            if (sat) sat = decide(1);
        } while (size_one_clauses != NULL);
        return sat;
    }

    // FIND VARIABLE WITH LARGEST VSIDS TO ASSIGN
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
        fprintf(stderr,
                "FAILED ASSERTION! ASSIGNING ALREADY ASSIGNED VARIABLE!\n");
        exit(1);
    }

    // TRY ASSIGNING, IN CASE OF SUCCESS MOVE TO THE NEXT DECISION LEVEL
    for (int assignment = 0; assignment < 2; assignment++) {
        num_branching++;

        implications[decision_level] = (malloc(2 * sizeof(int)));

        // for performance and simplicity reasons the number of implications
        // at current level is stored as a negative number at
        // index 0 of implications array
        implications[decision_level][0] = -1;
        implications[decision_level][1] = variable_id;

        // TRY ASSIGNING, IF SUCCESSFUL GO TO THE NEXT LEVEL
        int success = assign(variable_id, decision_level, assignment);

        if (success > 0) success = decide(decision_level + 1);
        if (success > 0) return 1;

        // NOT SUCCESSFUL, DECIDE WHERE TO BACKTRACK
        unassign(decision_level);

        // BACKTRACK TO HERE, TRY THIS ASSIGNMENT AGAIN, WITH NEW CONFLICT INFO
        if (success == VISIT_NONCHR_BACKTR) {
            assignment--;
        }

        // BACKTRACK FURTHER
        if (success < VISIT_NONCHR_BACKTR) {
            return success + 1;
        }
    }

    return 0;
}

int assign(int variable_id, int decision_level, int assignment) {

    // ACTUALLY ASSIGN LITERAL
    variables[variable_id].assignment = assignment;
    variables[variable_id].decision_level = decision_level;
    variables[variable_id].position_in_level =
        abs(implications[decision_level][0]) - 1;
    unassigned_count--;

    // TWO POINTERS FOR TRAVERSING LIST OF CLAUSES IN WHICH THE LITERAL
    // IS WATCHED. CLAUSES, WHERE THERE WAS FOUND ANOTHER LITERAL TO WATCH
    // SHOULD BE REMOVED FROM THE LIST
    int_list* to_update;
    int_list* crt;


    to_update = variables[variable_id].watched[assignment];
    crt = to_update;

    // KOCTbI/\b
    int sign = 1 - assignment * 2;

    while (to_update != NULL) {
        // TRY FINDING IN EACH CLAUSE ANOTHER LITERAL TO WATCH
        int result = replace_watched(to_update->int_data,
                variable_id * sign, decision_level);

        // IF JUST FOUND
        if (result == VISIT_NORMAL){
            // IF THIS WAS THE FIRST CLAUSE ON THE LIST, MOVE LITERAL'S
            // watched[x] POINTER TO THE NEXT, AND FREE THIS ONE
            if (to_update == variables[variable_id].watched[assignment]) {
                variables[variable_id].watched[assignment] = to_update->next;
                to_update = to_update->next;
                free(crt);
                crt = to_update;
            }
            // OTHERWISE REATTACH THE ->NEXT POINTER OF THE LAST PROCESSED
            // CLAUSE THAT WAS KEPT ON THE LIST TO THE NEXT CLAUSE TO BE
            // PROCESSED, AND ERASE THE ALREADY PROCESSED ONE, AND INCREMENT
            else {
                crt->next = to_update->next;
                free(to_update);
                to_update = crt->next;
            }
        }

        // IN CASE OF CONFLICT JUST STOP AND BACKTRACK
        // (BACKTRACKING DONE IN decide())
        else if (result <= VISIT_CONFLICT) {
            return result - VISIT_CONFLICT;
        }
        // IF THE LITERAL COULD'NT BE REPLACED, THEN CURRENT CLAUSE
        // WAS KEPT ON THE LIST, MOVE crt POINTER TO THIS ONE
        // AND INCREMENT to_update
        else {
            crt = to_update;
            to_update = to_update->next;
        }
    }

    // SUCCESS!
    return 1;
}

// NECESSARY CLEAN-UP FOR BACKTRACKING IS DONE HERE
void unassign(int decision_level) {

    decay_counter++;
    // PERIODICALLY DECAY VSIDS
    if (decay_counter == 50) {
        for (int i = 1; i <= num_variables; i++) {
            variables[i].vsids /= 2;
        }
        decay_counter = 0;
    }

    // ERASE ASSIGNMENT (try implementing vsids in here)
    for (int i = 1; i <= abs(implications[decision_level][0]); i++) {
        variables[implications[decision_level][i]].vsids++;
        variables[implications[decision_level][i]].assignment = -1;
        variables[implications[decision_level][i]].decision_level = -1;
        variables[implications[decision_level][i]].antecedent = -1;
        variables[implications[decision_level][i]].position_in_level = -1;
        unassigned_count++;
    }

    // CLEAR LIST OF THIS LEVEL ASSIGNMENTS
    free(implications[decision_level]);
    implications[decision_level] = NULL;
}

// to_replace: literal being replaced as watched,
// contains information whether watched pos or neg
int replace_watched(int to_visit, int to_replace, int decision_level) {

    clause* current = clauses + to_visit;
    // find another unassigned literal to watch
    // if none, check if resolved
    // if not resolved, check if unit -> imply
    // if not impliable -> learn conflict clause -> CONFLICT backtrack

    // FIRST OF ALL, LOOK FOR ANOTHER LITERAL TO WATCH
    for (int i = 0; i < current->size; i++) {

        // SINCE CLAUSE STORES LITERALS AS ID * SIGN,
        // ID and SIGN SHOULD BE FIRST CALCULATED
        int candidate = current->literals[i];
        int candidateID = abs(candidate);

        // watched positive or negarive
        int watched_p_n = candidate > 0 ? 0 : 1;
        int candidate_resolves = 0;

        // TRY TO DETERMINE IF WE CAN USE CANDIDATE AS ANOTHER WATCHED
        // BECAUSE IT RESOLVES THE CLAUSE
        if (variables[candidateID].assignment >= 0) {
            candidate_resolves =
                (variables[candidateID].assignment - watched_p_n) == 0 ? 0 : 1;
        }

        // IF IT EITHER RESOLVES OR UNASSIGNED AND NOT ANOTHER WATCHED LITERAL,
        // THEN WAS THE NORMAL CASE AND WE FOUND OUR LITERAL TO WATCH
        if ((candidate_resolves || variables[candidateID].assignment < 0)
                && index_of_element(candidate, current->watched, 0, 2) < 0) {
            attach_int_to_list(to_visit,
                    &(variables[candidateID].watched[watched_p_n]));
            current->watched[
                index_of_element( to_replace, current->watched, 0, 2)
            ] = candidate;
            return VISIT_NORMAL;
        }
    }

    // NOW LET'S HAVE A LOOK AT THE OTHER WATCHED LITERAL
    // aw FOR anotherWatched
    int aw = current->watched[
        1 - index_of_element(to_replace, current->watched, 0, 2)
    ];
    int aw_resolving_assignment = aw > 0 ? 1 : 0;
    int awID = abs(aw);

    // IF IT IS RESOLVING THIS CLAUSE THEN NO MORE WORK HERE
    if (variables[awID].assignment == aw_resolving_assignment) {
        return VISIT_RESOLVED;
    }

    // OR THERE IN AN IMPLICATION, IN CASE OF SUCCESSFUL IMPLICATION
    // RETURN VISIT_RESOLVED
    // ELSE PROPAGATE THE CONFLICT

    if (variables[awID].assignment < 0) {
        // determine how many implications were already done on this
        // (the 0th element holds negative size)
        int implications_size = abs(implications[decision_level][0]);

        // then resize the stuff appropriately
        implications_size++;
        implications[decision_level] = realloc(
                implications[decision_level],
                (implications_size + 1) * sizeof(int));

        // set the last implication to awID, which underwent implication
        implications[decision_level][implications_size] = awID;

        // then update 0th element to hold new size
        implications[decision_level][0] = -implications_size;

        // mark this clause as antecedent for this variable
        variables[awID].antecedent = to_visit;

        int implication_success = assign(
                awID, decision_level, aw_resolving_assignment);

        if (implication_success > 0) return VISIT_RESOLVED;
        else return VISIT_CONFLICT + implication_success;
    }

    // ANOTHER WATCH HAS ALSO ZEROING ASSIGNMENT, WHICH LEADS TO CONFLICT!
    if (decision_level == 0) return VISIT_CONFLICT;

    clause* learned_clause = first_uip(clauses + to_visit, decision_level);

    // FIND OUT SECOND LATEST DECISION LEVEL IN A LEARNED CLAUSE
    // TO BACKTRACK TO IF NOT FOUND, THEN LEARNED CLAUSE IS UNIT,
    // RETURN TO LEVEL ZERO AND ASSIGN
    int max_exc_current = 0;
    int this_level_var = 0;
    int latest_prev_var = 0;

    for (int i = 0; i < learned_clause->size; i++) {
        int check_var = learned_clause->literals[i];
        int max_candidate = variables[abs(check_var)].decision_level;
        if (max_candidate > max_exc_current &&
                max_candidate != decision_level) {
            latest_prev_var = check_var;
            max_exc_current = max_candidate;
        }
        if (max_candidate == decision_level) {
            this_level_var = check_var;
        }
    }

    // IT IS POSSIBLE THAT ALL VARIABLES EXCEPT FOR CURRENT LEVEL
    // VARIABLE WERE PRE-ASSIGNED
    // IN THIS CASE WE LEARNED NEW ASSIGNMENT (GO BACK TO LEVEL 1)
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

    // ADD NEWLY LEARNED CLAUSE TO GLOBAL DATABASE
    num_learned++;
    clauses = realloc(clauses, (num_clauses + 1) * sizeof(clause));
    clauses[num_clauses] = *learned_clause;

    free(learned_clause);

    // FINISH PROPER INITIALIZING OF THE CLAUSE
    if (clauses[num_clauses].size == 1) {
        clauses[num_clauses].watched[0] = 0;
        clauses[num_clauses].watched[1] = 0;
        attach_int_to_list(num_clauses, &size_one_clauses);
    }

    else {
        int to_watch[2];
        // most recently assigned variables should be watched
        // to effectively utilize non-chronological backtrack
        to_watch[0] = this_level_var;
        to_watch[1] = latest_prev_var;
        for (int watched_nr = 0; watched_nr < 2; watched_nr++) {
            clauses[num_clauses].watched[watched_nr] = to_watch[watched_nr];
            int attachID = to_watch[watched_nr];
            int p_o_n = attachID > 0 ? 0 : 1;
            attachID = abs(attachID);
            attach_int_to_list(
                    num_clauses, &(variables[attachID].watched[p_o_n]));
        }
    }
    num_clauses++;
    return VISIT_NONCHR_BACKTR + backtrack_levels;
}

// LEARN CLAUSE FROM CONFLICT USING FIRST UIP ALGORITHM
// RESOLVE conflict WITH THE MOST RECENT ASSIGNED VARIABLE's ANTECEDENT
// WHILE THERE ARE MORE THAN 1 VARIABLES ASSIGNED ON THE LAST DECISION LEVEL
// IN CLAUSE

clause* first_uip(clause* conflict, int decision_level) {

    clause* learn_result = malloc(sizeof(clause));

    // INITIALIZE NEW CLAUSE TO USE IN FIRST UIP
    // (EXPENDABLE, WILL BE OFTEN REALLOCATED)
    learn_result->size = conflict->size;
    learn_result->watched[0] = conflict->watched[0];
    learn_result->watched[1] = conflict->watched[1];
    learn_result->literals = malloc(sizeof(int) * conflict->size);
    for (int i = 0; i < conflict->size; i++) {
        learn_result->literals[i] = conflict->literals[i];
    }

    // nullify incoming clause pointer in order to not mess it up
    conflict = NULL;

    while (num_vars_from_level(learn_result, decision_level) > 1) {
        // FIND MOST RECENTLY ASSIGNED VARIABLE
        int most_recent = 0;
        for (int i = 0; i < learn_result->size; i++) {
            int candidate = abs(learn_result->literals[i]);
            if (variables[candidate].decision_level != decision_level) {
                continue;
            }
            if (most_recent == 0 ||
                    variables[candidate].position_in_level >
                    variables[abs(most_recent)].position_in_level) {
                most_recent = learn_result->literals[i];
            }
        }
        // RESOLVE NEW C AND THE VARIABLE's ANTECEDENT CLAUSE
        clause* resolvent = resolve(
                learn_result,
                clauses + variables[abs(most_recent)].antecedent,
                most_recent);
        free(learn_result->literals);
        free(learn_result);
        learn_result = resolvent;
    }
    return learn_result;
}

// THIS FUNCTION IMPLEMENTS RESOLUTION (a + b)(a' + c) = (a + b)(a' + c)(b + c)
// AND RETURNS POINTER TO (b + c)
clause* resolve(clause* conflict, clause* antecedent, int res_var) {
    clause* resolvent = malloc(sizeof(clause));
    resolvent->literals = malloc(0);

    int resolvent_size = 0;

    // ADD LITERALS FROM INITIATOR CLAUSE TO RESOLVING
    for (int i = 0; i < conflict->size; i++) {
        // this literal is valid to be in resolvent
        if (conflict->literals[i] != res_var) {
            resolvent->literals = realloc(
                    resolvent->literals,
                    sizeof(int) * (resolvent_size + 1));
            resolvent->literals[resolvent_size] = conflict->literals[i];
            resolvent_size++;
        }
    }

    // ADD LITERALS FROM ANTECEDENT CLAUSE TO RESOLVING
    for (int i = 0; i < antecedent->size; i++) {
        if (antecedent->literals[i] != -res_var &&
                index_of_element(
                    antecedent->literals[i],
                    resolvent->literals,
                    0,
                    resolvent_size) < 0) {
            resolvent->literals = realloc(
                    resolvent->literals, sizeof(int) * (resolvent_size + 1));
            resolvent->literals[resolvent_size] = antecedent->literals[i];
            resolvent_size++;
        }
    }
    resolvent->size = resolvent_size;
    return resolvent;
}

// THIS FUNCTION IS USED TO CREATE AN INSTANCE OF STRUCT int_list
// WITH data AS IT'S int_data AND ATTACH IT TO A LIST, POINTED BY attach_to
void attach_int_to_list(int data, int_list** attach_to) {

    int_list* new_list_el = (malloc(sizeof(int_list)));
    new_list_el->int_data = data;
    new_list_el->next = NULL;

    // ATTACH TO IS THE HEAD OF THE LIST
    int_list* tmp = *attach_to;

    // IF HEAD IS NULL MAKE NEW ELEMENT A HEAD
    if (tmp == NULL) {
        *attach_to = new_list_el;
        return;
    }

    // ELSE FIND TAIL AND HANG IT THERE
    while (tmp->next != NULL) {
        tmp = tmp->next;
    }
    tmp->next = new_list_el;
}
