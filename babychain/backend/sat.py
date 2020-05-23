import random
from typing import List


class Sat:
    @staticmethod
    def __generate_problem(num_vars: int = 3, num_clauses: int = 3) \
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

    @staticmethod
    def __get_problem_str(problem_list: List[List[str]]) -> str:
        """
        Converts the list of kCNF clauses to a string representation

        Parameters:
            problem_list: a list of kCNF clauses in the form
                generated by self.__generate_problem()

        Returns:
            str: a string representation where '|' and '&' are used to represent
                OR and AND relations
        """
        return '&'.join(['|'.join(clause) for clause in problem_list])

    @staticmethod
    def __parse(problem_str: str) -> List[List[str]]:
        """
        Parses the problem string into list representation

        Parameters:
            problem_str: a string representation in the form generated by
                self.__get_problem_str()

        Returns:
            List[List[str]]: a 2D list representation of the problem in the form
                generated by self.__generate_problem()
        """
        return [clause.split('|') for clause in problem_str.split('&')]
