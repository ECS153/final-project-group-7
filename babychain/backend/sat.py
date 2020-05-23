import random
from typing import List


class Sat:
    @staticmethod
    def generate_problem(num_vars: int = 3, num_clauses: int = 3) \
            -> List[List[str]]:
        """
        Generates and returns a SAT problem in kCNF form, where k=self.num_vars

        Parameters:
            num_vars: number of unique variables
            num_clauses: number of kCNF clauses

        Returns:
            List[List[str]]: a list of kCNF clauses(lists), and each str in the
                clause is an optional '!' followed by x[1-k]
        """
        candidate_vars = ['x' + str(i) for i in range(1, num_vars + 1)]
        prefixes = ['!', '']
        clauses = []

        # builds up each clause
        for i in range(num_clauses):
            random.shuffle(candidate_vars)
            curr_clause = []

            # builds up each variable in current clause
            for j in range(num_vars):
                prefix = random.choice(prefixes)
                curr_var = candidate_vars[j]
                curr_clause.append(prefix + curr_var)

            clauses.append(curr_clause)

        return clauses
