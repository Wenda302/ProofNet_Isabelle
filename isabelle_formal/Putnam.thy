theory Putnam
 imports Main
begin

(*
problem_number:2021_b4
natural language statement:
Let $F_{0}, F_{1}, \ldots$ be the sequence of Fibonacci numbers, with $F_{0}=0, F_{1}=1$, and $F_{n}=F_{n-1}+F_{n-2}$ for $n \geq 2$. For $m>2$, let $R_{m}$ be the remainder when the product $\prod_{k=1}^{F_{m}-1} k^{k}$ is divided by $F_{m}$. Prove that $R_{m}$ is also a Fibonacci number.
lean statement:

codex statement:
theorem fibonacci_of_product_mod_fibonacci:
  fixes m::nat
  assumes "m>2"
  shows "fib m ∣ (∏k=1..fib m - 1. k ^ k)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2021_b4: undefined oops


(*
problem_number:2020_b5
natural language statement:
For $j \in\{1,2,3,4\}$, let $z_{j}$ be a complex number with $\left|z_{j}\right|=1$ and $z_{j} \neq 1$. Prove that $3-z_{1}-z_{2}-z_{3}-z_{4}+z_{1} z_{2} z_{3} z_{4} \neq 0 .$
lean statement:

codex statement:
theorem sum_of_four_complex_number_neq_zero:
  fixes z::"complex set"
  assumes "card z = 4" "∀x∈z. norm x = 1" "∀x∈z. x ≠ 1"
  shows "3 - (∑x∈z. x) + (∏x∈z. x) ≠ 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2020_b5: undefined oops


(*
problem_number:2018_a5
natural language statement:
Let $f: \mathbb{R} \rightarrow \mathbb{R}$ be an infinitely differentiable function satisfying $f(0)=0, f(1)=1$, and $f(x) \geq 0$ for all $x \in$ $\mathbb{R}$. Show that there exist a positive integer $n$ and a real number $x$ such that $f^{(n)}(x)<0$.
lean statement:

codex statement:
theorem exists_n_x_of_derivative_neg:
  fixes f::"real ⇒ real"
  assumes "∀x. f differentiable (at x)" "f 0 = 0" "f 1 = 1" "∀x. 0 ≤ f x"
  shows "∃n x. (deriv ^^ n) f x < 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2018_a5: undefined oops


(*
problem_number:2018_b2
natural language statement:
Let $n$ be a positive integer, and let $f_{n}(z)=n+(n-1) z+$ $(n-2) z^{2}+\cdots+z^{n-1}$. Prove that $f_{n}$ has no roots in the closed unit disk $\{z \in \mathbb{C}:|z| \leq 1\}$.
lean statement:

codex statement:
theorem no_roots_in_closed_unit_disk:
  fixes n::nat and f::"complex ⇒ complex"
  assumes "n>0"
  shows "∀z. cmod z ≤ 1 ⟶ f z ≠ 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2018_b2: undefined oops


(*
problem_number:2018_b4
natural language statement:
Given a real number $a$, we define a sequence by $x_{0}=1$, $x_{1}=x_{2}=a$, and $x_{n+1}=2 x_{n} x_{n-1}-x_{n-2}$ for $n \geq 2$. Prove that if $x_{n}=0$ for some $n$, then the sequence is periodic.
lean statement:

codex statement:
theorem periodic_of_zero_in_seq:
  fixes a::real
  assumes "∃n. x n = 0"
  shows "∃m. ∀n. x (n+m) = x n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2018_b4: undefined oops


(*
problem_number:2018_b6
natural language statement:
Let $S$ be the set of sequences of length 2018 whose terms are in the set $\{1,2,3,4,5,6,10\}$ and sum to 3860 . Prove that the cardinality of $S$ is at most $2^{3860} \cdot\left(\frac{2018}{2048}\right)^{2018} .$
lean statement:

codex statement:
theorem card_set_of_sequences_leq_exp_of_sum_of_terms:
  fixes n::nat and S::"nat set"
  assumes "card S = 7" "n>0" "∀x∈S. x≤n"
  shows "card {x. set x ⊆ S ∧ length x = n ∧ sum_list x = m} ≤ 2^m * (n/2^nat_ceiling_log2 n)^n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2018_b6: undefined oops


(*
problem_number:2017_b3
natural language statement:
Suppose that $f(x)=\sum_{i=0}^{\infty} c_{i} x^{i}$ is a power series for which each coefficient $c_{i}$ is 0 or 1 . Show that if $f(2 / 3)=3 / 2$, then $f(1 / 2)$ must be irrational.
lean statement:

codex statement:
theorem irrational_of_power_series_eq_frac:
  fixes f::"real ⇒ real"
  assumes "∀x. f x = (∑i. c i * x^i)" "∀i. c i = (0::real) ∨ c i = 1" "f (2/3) = 3/2"
  shows "irrational (f (1/2))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2017_b3: undefined oops


(*
problem_number:2016_a6
natural language statement:
Suppose that $G$ is a finite group generated by the two elements $g$ and $h$, where the order of $g$ is odd. Show that every element of $G$ can be written in the form $g^{m_1} h^{n_1} g^{m_2} h^{n_2} \cdots g^{m_r} h^{n_r}$ with $1 \leq r \leq|G|$ and $m_1, n_1, m_2, n_2, \ldots, m_r, n_r \in$ $\{-1,1\} .$ (Here $|G|$ is the number of elements of $G$.)
lean statement:

codex statement:
theorem exists_odd_order_generator_of_finite_group:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "finite (carrier G)" "order G = n" "∃g. g ∈ carrier G ∧ order g = 2"
  shows "∃g. g ∈ carrier G ∧ order g = 2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2016_a6: undefined oops


(*
problem_number:2015_b1
natural language statement:
Let $f$ be a three times differentiable function (defined on $\mathbb{R}$ and real-valued) such that $f$ has at least five distinct real zeros. Prove that $f+6 f^{\prime}+12 f^{\prime \prime}+8 f^{\prime \prime \prime}$ has at least two distinct real zeros.
lean statement:

codex statement:

Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2015_b1: undefined oops




end