theory Prompt_Test imports 
  Main
  "HOL-Algebra.Algebra"
  "HOL-Analysis.Analysis"
begin

(*
Natural language version: "Let $P$ be a $p$-subgroup of $G$. Then $P$ is contained in a Sylow $p$-subgroup of $G$." Translate the natural language version to a Lean mathlib version: 
theorem exists_le_sylow {p : \<nat>} {G : Type*} [group G] {P : subgroup G} 
  (hP : is_p_group p P) :
  \<exists> (Q : sylow p G), P \<le> Q :=
*)
theorem exists_le_sylow:
  fixes p a m::nat and G::"('a, 'b) monoid_scheme"
  assumes "normalization_semidom_class.prime p" "group G" "order G = (p^a) * m" "finite (carrier G)"
  shows "\<exists>H. subgroup H G \<and> card H = p^a"
  oops

(*
Natural language version: "Let $E$ and $F$ be complex normed spaces and let $f:E\to F$. If $f$ is differentiable and bounded, then $f$ is constant." Translate the natural language version to a Lean mathlib version: 
theorem exists_eq_const_of_bounded {E : Type u} [normed_group E]
  [normed_space \<complex> E] {F : Type v} [normed_group F] [normed_space \<complex> F]
  {f : E \<rightarrow> F} (hf : differentiable \<complex> f) (hb : metric.bounded (set.range f)) :
  \<exists> (c : F), f = function.const E c :=
*)
theorem exists_eq_const_of_bounded:
  fixes  f::"complex \<Rightarrow> 'a::real_normed_vector"
  assumes "\<forall>x. f differentiable (at x)" "bounded (range f)"
  shows "f constant_on (UNIV::complex set)"
  oops

(*
Natural language version: "Let $X$ be a topological space; let $A$ be a subset of $X$. Suppose that for each $x\in A$ there is an open set $U$ containing $x$ such that $U\subset A$. Then $A$ is open in $X$." Translate the natural language version to a Lean mathlib version: 
theorem subset_of_open_subset_is_open (X : Type* ) [topological_space X]
  (A : set X) (hA : \<forall> x \<in> A, \<exists> U : set X, is_open U \<and> x \<in> U \<and> U \<subseteq> A): 
  is_open A :=
*)
theorem subset_of_open_subset_is_open:
  fixes T::"'a topology" and A::"'a set"
  assumes "A \<subseteq> topspace T" "\<forall>x\<in>A. \<exists> U \<subseteq> topspace T. openin T U \<and> x\<in>U \<and> U \<subseteq> A"
  shows "openin T A"
  oops


(*
Natural language version: "Two multiplicative functions $f, g:\mathbb{N}\to R$ are equal if and only if $f(p^i)=f(g^i)$ for all primes $p$." Translate the natural language version to a Lean mathlib version: 
theorem is_multiplicative.eq_iff_eq_on_prime_powers {R : Type*} 
  [comm_monoid_with_zero R] (f : nat.arithmetic_function R) 
  (hf : f.is_multiplicative) (g : nat.arithmetic_function R) 
  (hg : g.is_multiplicative) :
  f = g \<leftrightarrow> \<forall> (p i : \<nat>), nat.prime p \<rightarrow> f (p ^ i) = g (p ^ i) :=
*)
(*
I don't think we have a definition of multiplicative function yet.
*)


(*
Natural language version: "If $z_1, \\dots, z_n$ are complex, then $|z_1 + z_2 + \\dots + z_n|\\leq |z_1| + |z_2| + \\dots + |z_n|$." Translate the natural language version to a Lean mathlib version:
theorem abs_sum_leq_sum_abs (n : \<nat>) (f : \<nat> \<rightarrow> \<complex>) :
  abs (\<Sum> i in finset.range n, f i) \<le> \<Sum> i in finset.range n, abs (f i) :=
*)
theorem abs_sum_leq_sum_abs:
  fixes n::nat and f::"nat \<Rightarrow> complex"
  shows "abs (\<Sum>i<n. f i) \<le> (\<Sum>i<n. abs (f i))"
  oops

(*
Natural language version: "If x and y are in $\\mathbb{R}^n$, then $|x+y|^2 + |x-y|^2 = 2|x|^2 + 2|y|^2$." Translate the natural language version to a Lean mathlib version:
theorem sum_add_square_sub_square_eq_sum_square (n : \<nat>) (x y : euclidean_space \<real> (fin n)) :
  \<parallel>x + y\<parallel>^2 + \<parallel>x - y\<parallel>^2 = 2*\<parallel>x\<parallel>^2 + 2*\<parallel>y\<parallel>^2 :=
*)
theorem sum_add_square_sub_square_eq_sum_square:
  fixes x y::"'a::euclidean_space"
  shows "norm (x+y)^2 + norm (x - y) ^ 2 = 2 * (norm x)^2 + 2* (norm y)^2"
  oops

(*
Natural language version: "If $x$ is an element of infinite order in $G$, prove that the elements $x^n$, $n\\in\\mathbb{Z}$ are all distinct." Translate the natural language version to a Lean mathlib version:
theorem distinct_powers_of_infinite_order_element (G : Type* ) [group G] (x : G)
  (hx_inf : \<forall> n : \<nat>, x ^ n \<noteq> 1) :
  \<forall> m n : \<int>, m \<noteq> n \<rightarrow> x ^ m \<noteq> x ^ n :=
*)
theorem distinct_powers_of_infinite_order_element:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "\<forall>n ::nat. x [^] n \<noteq> \<one>"
  shows "\<forall> m n :: int. m \<noteq> n \<longrightarrow> x [^] m \<noteq> x [^] n"
  oops


(*
Natural language version "A set of vectors $\{v_i\}_{i\in I}$ orthogonal with respect 
to some bilinear form $B: V\times V\to K$ is linearly independent if for 
all $i \in I, B(v_i, v_i)\neq 0$." Translate the natural language version to a Lean mathlib version:
theorem linear_independent_of_is_Ortho {V K : Type*} [field K] 
  [add_comm_group V] [module K V] {n : Type*} {B : bilin_form K V} 
  {v : n \<rightarrow> V} (hv₁ : B.is_Ortho v) 
  (hv₂ : \<forall> (i : n), \<not>B.is_ortho (v i) (v i)) :
  linear_independent K v :=
*)
theorem linear_independent_of_is_Ortho:
  fixes B::"'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'b::real_vector"
  assumes "bilinear B" "pairwise (\<lambda>x y. B x y=0) v" "\<forall>x\<in>v. B x x\<noteq>0"
  shows "independent v"
  oops

(*
Natural language version: "Suppose that $V$ is an $n$-dimensional vector space. 
Then for some set of vectors $\{v_i\}_{i=1}^k$, if $k>n$ then there exist scalars $f_1, 
\dots, f_k$ such that $\sum_{i=1}^k f_kv_k = 0$." Translate the natural 
language version to a Lean mathlib version: 
theorem exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card {K V : Type*} 
  [division_ring K] [add_comm_group V] [module K V] [finite_dimensional K V] 
  {t : finset V} (h : finite_dimensional.finrank K V + 1 < t.card) :
  \<exists> (f : V \<rightarrow> K), t.sum (\<lambda> (e : V), f e • e) = 0 \<and> t.sum (\<lambda> (e : V), f e) = 0 
  \<and> \<exists> (x : V) (H : x \<in> t), f x \<noteq> 0 := 
*)
theorem exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card:
  fixes v::"'a::euclidean_space set"
  assumes "card v > DIM('a)"
  shows "\<exists>f. (\<Sum>x\<in>v. f x *\<^sub>R x) = 0 \<and> (\<exists>x\<in>v. f x\<noteq>0)"
  oops

(*
Natural language version: "A group is commutative if the quotient by the center is cyclic." Translate the natural language version to a Lean mathlib version: 
theorem comm_group_of_cycle_center_quotient {G H : Type*} [group G] [group H]
  [is_cyclic H] (f : G \<rightarrow>* H) (hf : f.ker \<le> center G) :
  comm_group G :=
*)
(*
we have 'cyclic_group' and 'comm_group' but I am not sure how to translate 'the quotient by the center'
*)


(*
Natural language version: "If $H$ is a $p$-subgroup of $G$, then the index of $H$ inside its normalizer is congruent modulo $p$ to the index of $H$." Translate the natural language version to a Lean mathlib version: 
theorem card_quotient_normalizer_modeq_card_quotient {G : Type*} [group G] 
  [fintype G] {p n : \<nat>} [hp : fact (nat.prime p)] {H : subgroup G} 
  (hH : card H = p ^ n) :
  card (H.normalizer / subgroup.comap H.normalizer.subtype H) \<equiv>  card (G / H) [MOD p] :=
*)
(*
Not sure how to translate this to HOL-Algebra
*)

(*Natural language version: "Suppose $X, Y, Z$ are metric spaces, and $Y$ is compact.
 Let $f$ map $X$ into $Y$, let $g$ be a continuous one-to-one mapping of $Y$ into $Z$, 
and put $h(x)=g(f(x))$ for $x \in X$. Prove that $f$ is uniformly 
continuous if $h$ is uniformly continuous." 
Translate the natural language version to a Lean mathlib version:
theorem uniform_continuous_of_continuous_injective_uniform_continuous_comp
  {X Y Z : Type*} [metric_space X] [metric_space Y] [metric_space Z]
  (hY : compact_space Y) (f : X \<rightarrow> Y) (g : Y \<rightarrow> Z) (hgc : continuous g)
  (hgi : function.injective g)
  (h : uniform_continuous (g \<circ> f)) : uniform_continuous f :=*)
theorem uniform_continuous_of_continuous_injective_uniform_continuous_comp:
  fixes f::"'a::metric_space \<Rightarrow> 'b::metric_space" and g::"'b::metric_space \<Rightarrow> 'c::metric_space"
  assumes "compact (UNIV::'b set)" "continuous_on UNIV g" "inj g" "uniformly_continuous_on UNIV (g \<circ> f)"
  shows "uniformly_continuous_on UNIV f"
  oops


theorem xxx: undefined


end