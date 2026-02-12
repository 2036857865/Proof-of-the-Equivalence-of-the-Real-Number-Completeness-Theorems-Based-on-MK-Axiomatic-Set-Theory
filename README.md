# Proof-of-the-Equivalence-of-the-Real-Number-Completeness-Theorems-Based-on-Morse-Kelley-Axiomatic-Set-Theory

The completeness theorems of real numbers are the foundation of calculus and mathematical analysis, playing a crucial role in the transition from calculus to analysis. These theorems have various formulations, and this paper formally characterizes the equivalence of multiple completeness theorems of real numbers based on the MK axiomatic set theory, including Dedekind's Fundamental Theorem, the Supremum Theorem, the Monotone Convergence Theorem, the Nested Interval Theorem, the Heine-Borel Theorem, the Bolzano-Weierstrass Theorem, and the Sequential Compactness Theorem.
Our work builds upon the MK axiomatic set theory and formal proofs in the foundations of analysis. Related links: https://github.com/bbLeng/Formalization-of-number-systems

Files
The proof is based on Morse-Kelley axiomatic set theory, which includes the following .v files:

Pre_MK_Logic.v

MK_Structure1.v (* Depends on Pre_MK_Logic.v *)

MK_Theorems1.v (* Depends on MK_Structure1.v *)

FA_R1.v (* Depends on MK_Theorems1.v *)

Sup_Inf_Principle.v (* Depends on FA_R1.v *)

Dedekind_Theorem_Proof_By_Sup_Inf_Principle.v (* Depends on Sup_Inf_Principle.v *)

Monotone_Bounded_Theorem.v (* Depends on Dedekind_Theorem_Proof_By_Sup_Inf_Principle.v *)

Archimedean_Theorems1.v (* Depends on Monotone_Bounded_Theorem.v *)

Nested_Closed_Interval_Theorem.v (* Depends on Monotone_Bounded_Theorem.v *)

Finite_Covering_Theorem.v (* Depends on Nested_Closed_Interval_Theorem.v *)

Bolzano_Weierstrass_Theorem.v (* Depends on Finite_Covering_Theorem.v *)

Archimedean_Theorems2.v (* Depends on Bolzano_Weierstrass_Theorem.v *)

Sequential_Compactness_Theorem.v (* Depends on Archimedean_Theorems2.v *)

Cauchy_Convergence_Criterion.v (* Depends on Sequential_Compactness_Theorem.v *)

Dedekind_Theorem_Proof_By_Cauchy_Convergence_Criterion.v (* Depends on Cauchy_Convergence_Criterion.v *)


Authors
This project is implemented by Ce Zhang, Guowei Dou, Wensheng Yu.
