# Proof-of-the-Equivalence-of-the-Real-Number-Completeness-Theorems-Based-on-Morse-Kelley-Axiomatic-Set-Theory

This project is based on Morse-Kelley (MK) axiomatic set theory and strictly follows the method of constructing number systems in Landau's Foundations of Analysis, thus completing a series of formalization work on the fundamentals of mathematical analysis, including the formal definition and verification of the recursion theorem and exponential functions, the formal proof of the Archimedean property of real numbers in various forms, and the completion of a cyclic formal proof of the equivalence of the eight theorems on the completeness of real numbers (including Dedekind's Fundamental Theorem) with Dedekind's Fundamental Theorem as the logical starting point, which has constructed a comprehensive formal system for the completeness of real numbers. This project is fully based on the formalization of MK axiomatic set theory and the formalization of the real number system in Landau's Foundations of Analysis, without adding any axioms other than those of MK axiomatic set theory. Related links: https://github.com/bbLeng/Formalization-of-number-systems

All proofs are based on Rocq (Coq) 8.20.1.

# Files
The proof is based on Morse-Kelley axiomatic set theory, which includes the following .v files:

Pre_MK_Logic.v

MK_Structure1.v (* Depends on Pre_MK_Logic.v *)

MK_Theorems1.v (* Depends on MK_Structure1.v *)

FA_R1.v (* Depends on MK_Theorems1.v *)

Sup_Inf_Principle.v (* Depends on FA_R1.v *)

Dedekind_Theorem_Proof_By_Sup_Inf_Principle.v (* Depends on Sup_Inf_Principle.v *)

Monotone_Bounded_Theorem.v (* Depends on Dedekind_Theorem_Proof_By_Sup_Inf_Principle.v *)

Archimedean_Theorems1.v (* Depends on Monotone_Bounded_Theorem.v *)

Nested_Closed_Interval_Theorem.v (* Depends on Archimedean_Theorems1.v *)

Finite_Covering_Theorem.v (* Depends on Nested_Closed_Interval_Theorem.v *)

Bolzano_Weierstrass_Theorem.v (* Depends on Finite_Covering_Theorem.v *)

Archimedean_Theorems2.v (* Depends on Bolzano_Weierstrass_Theorem.v *)

Sequential_Compactness_Theorem.v (* Depends on Archimedean_Theorems2.v *)

Cauchy_Convergence_Criterion.v (* Depends on Sequential_Compactness_Theorem.v *)

Dedekind_Theorem_Proof_By_Cauchy_Convergence_Criterion.v (* Depends on Cauchy_Convergence_Criterion.v *)


# Authors
This project is implemented by Ce Zhang, Guowei Dou, Wensheng Yu.
