# Graffiti.pc 392b on 2-domination and matchings

Tomás Correia · AI-assisted proof and formalization with Codex.

Choose vertices in a network so that every unchosen vertex has two chosen neighbors. Conjecture 392b gives an upper bound on how many vertices suffice. Delete all vertices of minimum degree and count a largest matching in the remaining graph. Add the number of deleted vertices and the number of original vertices with exactly one neighbor of degree two. The theorem proves this bound for every connected finite simple graph with more than two vertices, including graphs with leaves.

Challenge.lean specifies the graph, the invariants, and the inequality. Solution.lean contains the complete proof. Build the two targets separately with Lake. The deliberate placeholder in Challenge.lean represents the statement supplied to Comparator. The proof in Solution.lean has no placeholders.

[Published proof, examples, and prior work](https://doi.org/10.5281/zenodo.24571980)
