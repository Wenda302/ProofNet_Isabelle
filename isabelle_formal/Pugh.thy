theory Pugh
 imports Main
begin

(*
problem_number:2_12a
natural language statement:
Let $(p_n)$ be a sequence and $f:\mathbb{N}\to\mathbb{N}$ a bijection. The sequence $(q_k)_{k\in\mathbb{N}}$ with $q_k=p_{f(k)}$ is called a rearrangement of $(p_n)$. Show that if $f$ is an injection, the limit of a sequence is unaffected by rearrangement.
lean statement:
theorem exercise_2_12a (f : \<nat> \<rightarrow> \<nat>) (p : \<nat> \<rightarrow> \<real>) (a : \<real>)
  (hf : injective f) (hp : tendsto p at_top (𝓝 a)) :
  tendsto (\<lambda> n, p (f n)) at_top (𝓝 a) :=

codex statement:
theorem lim_of_rearrangement_of_injective:
  fixes f::"nat \<Rightarrow> nat" and p::"nat \<Rightarrow> 'a::real_normed_vector"
  assumes "inj f" "convergent p"
  shows "convergent (\<lambda>n. p (f n))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_12a: undefined oops


(*
problem_number:2_12b
natural language statement:
Let $(p_n)$ be a sequence and $f:\mathbb{N}\to\mathbb{N}$ a bijection. The sequence $(q_k)_{k\in\mathbb{N}}$ with $q_k=p_{f(k)}$ is called a rearrangement of $(p_n)$. Show that if $f$ is a surjection, the limit of a sequence is unaffected by rearrangement.
lean statement:
theorem exercise_2_12b (f : \<nat> \<rightarrow> \<nat>) (p : \<nat> \<rightarrow> \<real>) (a : \<real>)
  (hf : surjective f) (hp : tendsto p at_top (𝓝 a)) :
  tendsto (\<lambda> n, p (f n)) at_top (𝓝 a) :=

codex statement:
theorem lim_of_rearrangement_of_surjection:
  fixes f::"nat \<Rightarrow> nat" and p::"nat \<Rightarrow> 'a::real_normed_vector"
  assumes "bij f" "surj f" "\<forall>n. p n = q (f n)" "convergent p"
  shows "convergent q \<and> lim p = lim q"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_12b: undefined oops


(*
problem_number:2_26
natural language statement:
Prove that a set $U \subset M$ is open if and only if none of its points are limits of its complement.
lean statement:
theorem exercise_2_26 {M : Type*} [topological_space M]
  (U : set M) : is_open U \<longleftrightarrow> \<forall> x \<in> U, ¬ cluster_pt x (𝓟 Uᶜ) :=

codex statement:
theorem open_iff_no_limit_point_of_complement:
  fixes U::"'a::metric_space set"
  shows "open U \<longleftrightarrow> \<forall>x\<in>U. ¬(x islimpt (-U))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_26: undefined oops


(*
problem_number:2_29
natural language statement:
Let $\mathcal{T}$ be the collection of open subsets of a metric space $\mathrm{M}$, and $\mathcal{K}$ the collection of closed subsets. Show that there is a bijection from $\mathcal{T}$ onto $\mathcal{K}$.
lean statement:
theorem exercise_2_29 (M : Type* ) [metric_space M]
  (O C : set (set M))
  (hO : O = {s | is_open s})
  (hC : C = {s | is_closed s}) :
  \<exists> f : O \<rightarrow> C, bijective f :=

codex statement:
theorem bijection_open_closed:
  fixes M::"'a::metric_space set"
  shows "bij_betw (\<lambda>U. closure U) (open_sets M) (closed_sets M)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_29: undefined oops


(*
problem_number:2_32a
natural language statement:
Show that every subset of $\mathbb{N}$ is clopen.
lean statement:
theorem exercise_2_32a (A : set \<nat>) : is_clopen A :=

codex statement:
theorem clopen_of_subset_nat:
  fixes A::"nat set"
  shows "closed_in (top_of_set UNIV) A \<and> open_in (top_of_set UNIV) A"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_32a: undefined oops


(*
problem_number:2_41
natural language statement:
Let $\|\cdot\|$ be any norm on $\mathbb{R}^{m}$ and let $B=\left\{x \in \mathbb{R}^{m}:\|x\| \leq 1\right\}$. Prove that $B$ is compact.
lean statement:
theorem exercise_2_41 (m : \<nat>) {X : Type*} [normed_space \<real> ((fin m) \<rightarrow> \<real>)] :
  is_compact (metric.closed_ball 0 1) :=

codex statement:
theorem compact_of_norm_leq_one:
  fixes m::nat and f::"nat \<Rightarrow> real"
  assumes "norm f \<le> 1"
  shows "compact {x::'a::euclidean_space. \<forall>i. norm (x$i) \<le> f i}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_41: undefined oops


(*
problem_number:2_46
natural language statement:
Assume that $A, B$ are compact, disjoint, nonempty subsets of $M$. Prove that there are $a_0 \in A$ and $b_0 \in B$ such that for all $a \in A$ and $b \in B$ we have $d(a_0, b_0) \leq d(a, b)$.
lean statement:
theorem exercise_2_46 {M : Type*} [metric_space M]
  {A B : set M} (hA : is_compact A) (hB : is_compact B)
  (hAB : disjoint A B) (hA₀ : A \<noteq> \<emptyset>) (hB₀ : B \<noteq> \<emptyset>) :
  \<exists> a₀ b₀, a₀ \<in> A \<and> b₀ \<in> B \<and> \<forall> (a : M) (b : M),
  a \<in> A \<rightarrow> b \<in> B \<rightarrow> dist a₀ b₀ \<le> dist a b :=

codex statement:
theorem exists_min_distance_of_compact_disjoint_nonempty:
  fixes A B::"'a::metric_space set"
  assumes "compact A" "compact B" "A \<inter> B = {}" "A \<noteq> {}" "B \<noteq> {}"
  shows "\<exists>a b. a\<in>A \<and> b\<in>B \<and> (\<forall>a'\<in>A. \<forall>b'\<in>B. dist a b \<le> dist a' b')"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_46: undefined oops


(*
problem_number:2_48
natural language statement:
Prove that there is an embedding of the line as a closed subset of the plane, and there is an embedding of the line as a bounded subset of the plane, but there is no embedding of the line as a closed and bounded subset of the plane.
lean statement:

codex statement:
theorem exists_embedding_of_line_as_closed_subset_of_plane:
  fixes f::"real \<Rightarrow> 'a::euclidean_space"
  assumes "continuous_on UNIV f" "inj_on f UNIV" "f ` UNIV \<subseteq> (UNIV::'a set)"
  shows "closedin (subtopology euclidean (UNIV::'a set)) (f ` UNIV)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_48: undefined oops


(*
problem_number:2_56
natural language statement:
Prove that the 2-sphere is not homeomorphic to the plane.
lean statement:

codex statement:
theorem sphere_not_homeomorphic_to_plane:
  fixes S::"real^2 set"
  assumes "S homeomorphic (sphere (0,1))"
  shows False
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_56: undefined oops


(*
problem_number:2_57
natural language statement:
Show that if $S$ is connected, it is not true in general that its interior is connected.
lean statement:
theorem exercise_2_57 {X : Type*} [topological_space X]
  : \<exists> (S : set X), is_connected S \<and> ¬ is_connected (interior S) :=

codex statement:
theorem interior_not_connected_of_connected:
  fixes S::"'a::euclidean_space set"
  assumes "connected S"
  shows "\<exists>T. open T \<and> connected T \<and> interior T \<subseteq> S \<and> interior T \<noteq> \<emptyset> \<and> interior T \<noteq> S"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_57: undefined oops


(*
problem_number:2_79
natural language statement:
Prove that if $M$ is nonempty compact, locally path-connected and connected then it is path-connected.
lean statement:
theorem exercise_2_79
  {M : Type*} [topological_space M] [compact_space M]
  [loc_path_connected_space M] (hM : nonempty M)
  (hM : connected_space M) : path_connected_space M :=

codex statement:
theorem path_connected_of_nonempty_compact_locally_path_connected_connected:
  fixes M::"'a::topological_space set"
  assumes "compact M" "nonempty M" "locally path_connected M" "connected M"
  shows "path_connected M"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_79: undefined oops


(*
problem_number:2_85
natural language statement:
Suppose that $M$ is compact and that $\mathcal{U}$ is an open covering of $M$ which is redundant in the sense that each $p \in M$ is contained in at least two members of $\mathcal{U}$. Show that $\mathcal{U}$ reduces to a finite subcovering with the same property.
lean statement:
theorem exercise_2_85
  (M : Type* ) [topological_space M] [compact_space M]
  (U : set (set M)) (hU : \<forall> p, \<exists> (U_1 U_2 \<in> U), p \<in> U_1 \<and> p \<in> U_2 \<and> U_1 \<noteq> U_2) :
  \<exists> (V : set (set M)), set.finite V \<and>
  \<forall> p, \<exists> (V_1 V_2 \<in> V), p \<in> V_1 \<and> p \<in> V_2 \<and> V_1 \<noteq> V_2 :=

codex statement:
theorem finite_subcovering_of_redundant_open_covering:
  fixes M::"'a::metric_space set" and U::"'a set set"
  assumes "compact M" "\<forall>p\<in>M. \<exists>U_1 U_2. U_1\<in>U \<and> U_2\<in>U \<and> p\<in>U_1 \<and> p\<in>U_2"
  shows "\<exists>U'. finite U' \<and> U' \<subseteq> U \<and> \<forall>p\<in>M. \<exists>U_1 U_2. U_1\<in>U' \<and> U_2\<in>U' \<and> p\<in>U_1 \<and> p\<in>U_2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_85: undefined oops


(*
problem_number:2_92
natural language statement:
Give a direct proof that the nested decreasing intersection of nonempty covering compact sets is nonempty.
lean statement:
theorem exercise_2_92 {\<alpha> : Type*} [topological_space \<alpha>]
  {s : \<nat> \<rightarrow> set \<alpha>}
  (hs : \<forall> i, is_compact (s i))
  (hs : \<forall> i, (s i).nonempty)
  (hs : \<forall> i, (s i) ⊃ (s (i + 1))) :
  (\<Inter> i, s i).nonempty :=

codex statement:
theorem nonempty_intersection_of_nested_compact_covering_sets:
  fixes K::"nat \<Rightarrow> 'a::metric_space set"
  assumes "\<forall>n. compact (K n)" "\<forall>n. K n \<subseteq> K (Suc n)" "\<forall>n. K n \<noteq> {}"
  shows "\<exists>x. \<forall>n. x \<in> K n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_92: undefined oops


(*
problem_number:2_109
natural language statement:
A metric on $M$ is an ultrametric if for all $x, y, z \in M$, $d(x, z) \leq \max \{d(x, y), d(y, z)\} .$ Show that a metric space with an ultrametric is totally disconnected.
lean statement:
theorem exercise_2_109
  {M : Type*} [metric_space M]
  (h : \<forall> x y z : M, dist x z = max (dist x y) (dist y z)) :
  totally_disconnected_space M :=

codex statement:
theorem totally_disconnected_of_ultrametric:
  fixes M::"'a::metric_space metric"
  assumes "\<forall>x y z. dist x z \<le> max (dist x y) (dist y z)"
  shows "totally_disconnected (UNIV::'a set)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_109: undefined oops


(*
problem_number:2_126
natural language statement:
Suppose that $E$ is an uncountable subset of $\mathbb{R}$. Prove that there exists a point $p \in \mathbb{R}$ at which $E$ condenses.
lean statement:
theorem exercise_2_126 {E : set \<real>}
  (hE : ¬ set.countable E) : \<exists> (p : \<real>), cluster_pt p (𝓟 E) :=

codex statement:
theorem exists_condensation_point_of_uncountable_subset:
  fixes E::"real set"
  assumes "uncountable E"
  shows "\<exists>p. condensation_point E p"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_126: undefined oops


(*
problem_number:2_137
natural language statement:
Let $P$ be a closed perfect subset of a separable complete metric space $M$. Prove that each point of $P$ is a condensation point of $P$.
lean statement:
theorem exercise_2_137
  {M : Type*} [metric_space M] [separable_space M] [complete_space M]
  {P : set M} (hP : is_closed P)
  (hP' : is_closed P \<and> P = {x | cluster_pt x (𝓟 P)}) :
  \<forall> x \<in> P, \<forall> n \<in> (𝓝 x), ¬ set.countable n :=

codex statement:
theorem condensation_point_of_closed_perfect_subset:
  fixes P::"'a::metric_space set"
  assumes "closed P" "perfect P" "separable (UNIV::'a set)"
  shows "\<forall>x\<in>P. condensation_point P x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_137: undefined oops


(*
problem_number:2_138
natural language statement:
Given a Cantor space $M \subset R^2$, given a line segment $[p, q] \subset R^2$ with $p, q \not\in M$, and given an $\epsilon > 0$, prove that there exists a path $A$ in the $\epsilon$-neighborhood of $[p, q]$ that joins $p$ to $q$ and is disjoint from $M$.
lean statement:

codex statement:
theorem exists_path_disjoint_of_Cantor_space:
  fixes M::"real set" and p q::"real^2" and \<epsilon>::real
  assumes "Cantor_space M" "p \<in> (UNIV::real^2 set) - M" "q \<in> (UNIV::real^2 set) - M" "\<epsilon> > 0"
  shows "\<exists>A. path A \<and> path_image A \<subseteq> ball p \<epsilon> ∪ ball q \<epsilon> \<and> pathstart A = p \<and> pathfinish A = q \<and> path_image A ∩ M = {}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_138: undefined oops


(*
problem_number:3_1
natural language statement:
Assume that $f \colon \mathbb{R} \rightarrow \mathbb{R}$ satisfies $|f(t)-f(x)| \leq|t-x|^{2}$ for all $t, x$. Prove that $f$ is constant.
lean statement:
theorem exercise_3_1 {f : \<real> \<rightarrow> \<real>}
  (hf : \<forall> x y, |f x - f y| \<le> |x - y| ^ 2) :
  \<exists> c, f = \<lambda> x, c :=

codex statement:
theorem constant_of_abs_diff_leq_square_diff:
  fixes f::"real \<Rightarrow> real"
  assumes "\<forall>x t. abs (f t - f x) \<le> (abs (t - x))^2"
  shows "f constant_on UNIV"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_1: undefined oops


(*
problem_number:3_4
natural language statement:
Prove that $\sqrt{n+1}-\sqrt{n} \rightarrow 0$ as $n \rightarrow \infty$.
lean statement:
theorem exercise_3_4 (n : \<nat>) :
  tendsto (\<lambda> n, (sqrt (n + 1) - sqrt n)) at_top (𝓝 0) :=

codex statement:
theorem sqrt_succ_sub_sqrt_tendsto_zero:
  shows "(\<Sum>i=0..n. 1/(sqrt (real (Suc i)) + sqrt (real i))) \<longrightarrow> 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_4: undefined oops


(*
problem_number:3_11a
natural language statement:
Let $f \colon (a, b) \rightarrow \mathbb{R}$ be given.  If $f''(x)$ exists, prove that \[\lim_{h \rightarrow 0} \frac{f(x - h) - 2f(x) + f(x + h)}{h^2} = f''(x).\]
lean statement:
theorem exercise_3_11a
  {f : \<real> \<rightarrow> \<real>} {a b x : \<real>}
  (h1 : differentiable_within_at \<real> f (set.Ioo a b) x)
  (h2 : differentiable_within_at \<real> (deriv f) (set.Ioo a b) x) :
  \<exists> l, tendsto (\<lambda> h, (f (x - h) - 2 * f x + f (x + h)) / h ^ 2) (𝓝 0) (𝓝 l)
  \<and> deriv (deriv f) x = l :=

codex statement:
theorem limit_of_diff_of_diff_eq_diff_of_diff:
  fixes f::"real \<Rightarrow> real"
  assumes "\<forall>x. (f has_real_derivative f' x) (at x)" "\<forall>x. (f has_real_derivative f'' x) (at x)"
  shows "(f'' ---> f'' x) (at x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_11a: undefined oops


(*
problem_number:3_17c-i
natural language statement:
Show that the bump function $\beta(x)=e^{2} e(1-x) \cdot e(x+1)$ is smooth.
lean statement:

codex statement:
theorem smooth_of_bump_function:
  fixes x::real
  assumes "x\<in>{-1..1}"
  shows "\<forall>n. (∂^n) (\<lambda>x. exp 2 * exp (-x) * exp (x+1)) x = exp 2 * exp (-x) * exp (x+1)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_3_17c-i": undefined oops


(*
problem_number:3_17c-ii
natural language statement:
Show that the bump function $\beta(x)=e^{2} e(1-x) \cdot e(x+1)$ is identically 0 outside the interval $(-1, 1)$.
lean statement:

codex statement:
theorem bump_function_is_zero_outside_interval:
  fixes x::real
  shows "x\<le>-1 \<or> x\<ge>1 \<longrightarrow> (\<lambda>x. exp 2 * exp (-x) * exp (x+1)) x = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_3_17c-ii": undefined oops


(*
problem_number:3_18
natural language statement:
Let $L$ be any closed set in $\mathbb{R}$. Prove that there is a smooth function $f \colon \mathbb{R} \rightarrow [0, 1]$ such that $f(x) = 0$ if and only if $x \in L$.
lean statement:

codex statement:
theorem exists_smooth_function_of_closed_set:
  fixes L::"real set"
  assumes "closed L"
  shows "\<exists>f. (\<forall>x. f x = 0 \<longleftrightarrow> x\<in>L) \<and> (\<forall>x. f differentiable (at x))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_18: undefined oops


(*
problem_number:3_43a
natural language statement:
Let $\psi(x) = x \sin 1/x$ for $0 < x \leq 1$ and $\psi(0) = 0$.  If $f \colon [-1, 1] \rightarrow \mathbb{R}$ is Riemann integrable, prove that $f \circ \psi$ is Riemann integrable.
lean statement:

codex statement:
theorem riemann_integrable_of_riemann_integrable_comp:
  fixes f::"real \<Rightarrow> real" and ψ::"real \<Rightarrow> real"
  assumes "continuous_on {0..1} ψ" "f integrable_on {-1..1}"
  shows "(f ∘ ψ) integrable_on {0..1}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_43a: undefined oops


(*
problem_number:3_53
natural language statement:
Given $f, g \in \mathcal{R}$, prove that $\max(f, g)$ and $\min(f, g)$ are Riemann integrable, where $\max(f, g)(x) = \max(f(x), g(x))$ and $\min(f, g)(x) = \min(f(x), g(x))$.
lean statement:

codex statement:
theorem max_min_integrable:
  fixes f g::"real \<Rightarrow> real"
  assumes "f integrable_on {a..b}" "g integrable_on {a..b}"
  shows "(\<lambda>x. max (f x) (g x)) integrable_on {a..b}" "(\<lambda>x. min (f x) (g x)) integrable_on {a..b}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_53: undefined oops


(*
problem_number:3_59
natural language statement:
Prove that if $a_n \geq 0$ and $\sum a_n$ converges then $\sum \sqrt{a_n}/n$ converges.
lean statement:

codex statement:
theorem convergent_of_convergent_sum_sqrt_div_n:
  fixes a::"nat \<Rightarrow> real"
  assumes "\<forall>n. 0 \<le> a n" "summable a"
  shows "summable (\<lambda>n. sqrt (a n) / n)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_59: undefined oops


(*
problem_number:3_63
natural language statement:
Prove that $\sum 1/k(\log(k))^p$ converges when $p > 1$ and diverges when $p \leq 1$.
lean statement:
theorem exercise_3_63a (p : \<real>) (f : \<nat> \<rightarrow> \<real>) (hp : p > 1)
  (h : f = \<lambda> k, (1 : \<real>) / (k * (log k) ^ p)) :
  \<exists> l, tendsto f at_top (𝓝 l) :=

codex statement:
theorem sum_of_inverse_log_pow_p_converges_of_p_gt_1:
  fixes p::real
  assumes "p > 1"
  shows "summable (\<lambda>n. 1 / (real n * (log (real n)) ^ p))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_63: undefined oops


(*
problem_number:4_15a
natural language statement:
A continuous, strictly increasing function $\mu \colon (0, \infty) \rightarrow (0, \infty)$ is a modulus of continuity if $\mu(s) \rightarrow 0$ as $s \rightarrow 0$. A function $f \colon [a, b] \rightarrow \mathbb{R}$ has modulus of continuity $\mu$ if $|f(s) - f(t)| \leq \mu(|s - t|)$ for all $s, t \in [a, b]$. Prove that a function is uniformly continuous if and only if it has a modulus of continuity.
lean statement:
theorem exercise_4_15a {\<alpha> : Type*}
  (a b : \<real>) (F : set (\<real> \<rightarrow> \<real>)) :
  (\<forall> (x : \<real>) (\<epsilon> > 0), \<exists> (U \<in> (𝓝 x)),
  (\<forall> (y z \<in> U) (f : \<real> \<rightarrow> \<real>), f \<in> F \<rightarrow> (dist (f y) (f z) < \<epsilon>)))
  \<longleftrightarrow>
  \<exists> (\<mu> : \<real> \<rightarrow> \<real>), \<forall> (x : \<real>), (0 : \<real>) \<le> \<mu> x \<and> tendsto \<mu> (𝓝 0) (𝓝 0) \<and>
  (\<forall> (s t : \<real>) (f : \<real> \<rightarrow> \<real>), f \<in> F \<rightarrow> |(f s) - (f t)| \<le> \<mu> (|s - t|)) :=

codex statement:
theorem uniform_continuous_iff_has_modulus_of_continuity:
  fixes f::"'a::metric_space \<Rightarrow> 'b::metric_space" and \<mu>::"'a \<Rightarrow> 'b"
  assumes "continuous_on UNIV \<mu>" "strict_mono \<mu>" "\<mu> \<longrightarrow> 0 at_top" "\<forall>s t. s \<in> UNIV \<longrightarrow> t \<in> UNIV \<longrightarrow> dist s t \<le> \<mu> (dist s t)"
  shows "uniformly_continuous_on UNIV f"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_15a: undefined oops


(*
problem_number:4_15b
natural language statement:
A continuous, strictly increasing function $\mu \colon (0, \infty) \rightarrow (0, \infty)$ is a modulus of continuity if $\mu(s) \rightarrow 0$ as $s \rightarrow 0$. A function $f \colon [a, b] \rightarrow \mathbb{R}$ has modulus of continuity $\mu$ if $|f(s) - f(t)| \leq \mu(|s - t|)$ for all $s, t \in [a, b]$. Prove that a family of functions is equicontinuous if and only if its members.
lean statement:

codex statement:
theorem equicontinuous_of_modulus_of_continuity:
  fixes f::"'a::metric_space \<Rightarrow> 'b::metric_space" and g::"'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "\<forall>x. continuous (at x) f" "\<forall>x. continuous (at x) g" "\<forall>x. continuous (at x within s) f" "\<forall>x. continuous (at x within s) g"
  shows "uniformly_continuous_on s f" "uniformly_continuous_on s g"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_15b: undefined oops


(*
problem_number:4_19
natural language statement:
If $M$ is compact and $A$ is dense in $M$, prove that for each $\delta > 0$ there is a finite subset $\{a_1, \ldots , a_k\} \subset A$ which is $\delta$-dense in $M$ in the sense that each $x \in M$ lies within distance $\delta$ of at least one of the points $a_1,\ldots, a_k$.
lean statement:
theorem exercise_4_19 {M : Type*} [metric_space M]
  [compact_space M] (A : set M) (hA : dense A) (δ : \<real>) (hδ : δ > 0) :
  \<exists> (A_fin : set M), A_fin ⊂ A \<and> set.finite A_fin \<and> \<forall> (x : M), \<exists> i \<in> A_fin, dist x i < δ :=

codex statement:
theorem exists_finite_delta_dense_of_compact_dense:
  fixes M::"'a::metric_space set" and A::"'a set"
  assumes "compact M" "A \<subseteq> M" "dense A"
  shows "\<exists>A'. finite A' \<and> A' \<subseteq> A \<and> \<forall>x\<in>M. \<exists>a\<in>A'. dist x a < δ"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_19: undefined oops


(*
problem_number:4_36a
natural language statement:
Suppose that the ODE $x' = f(x)$ on $\mathbb{R}$ is bounded, $|f(x)| \leq M$ for all x. Prove that no solution of the ODE escapes to infinity in finite time.
lean statement:

codex statement:
theorem no_solution_escapes_to_infinity_in_finite_time:
  fixes f::"real \<Rightarrow> real"
  assumes "\<forall>x. abs (f x) \<le> M"
  shows "\<forall>x0 t. \<exists>x. x0 + t * f x0 = x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_36a: undefined oops


(*
problem_number:4_42
natural language statement:
Prove that $\mathbb{R}$ cannot be expressed as the countable union of Cantor sets.
lean statement:

codex statement:
theorem cantor_set_not_union_of_countable_cantor_sets:
  fixes C::"real set"
  assumes "\<forall>x\<in>C. \<exists>a b. x = a + b \<and> a \<in> cantor \<and> b \<in> cantor" "countable C"
  shows "False"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_42: undefined oops


(*
problem_number:5_2
natural language statement:
Let $L$ be the vector space of continuous linear transformations from a normed space $V$ to a normed space $W$. Show that the operator norm makes $L$ a normed space.
lean statement:
theorem exercise_5_2 {V : Type*} [normed_add_comm_group V]
  [normed_space \<complex> V] {W : Type*} [normed_add_comm_group W] [normed_space \<complex> W] :
  normed_space \<complex> (continuous_linear_map (id \<complex>) V W) :=

codex statement:
theorem norm_of_linear_transformation_is_norm:
  fixes V::"'a::real_normed_vector normed_vector" and W::"'b::real_normed_vector normed_vector"
  assumes "linear f"
  shows "norm f = ∥f∥"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_2: undefined oops


(*
problem_number:5_20
natural language statement:
Assume that $U$ is a connected open subset of $\mathbb{R}^n$ and $f \colon U \rightarrow \mathbb{R}^m$ is differentiable everywhere on $U$. If $(Df)_p = 0$ for all $p \in U$, show that $f$ is constant.
lean statement:

codex statement:
theorem constant_of_differentiable_zero:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "connected U" "open U" "\<forall>x\<in>U. f differentiable (at x)" "\<forall>x\<in>U. (D f) x = 0"
  shows "f constant_on U"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_20: undefined oops


(*
problem_number:5_22
natural language statement:
If $Y$ is a metric space and $f \colon [a, b] \times Y \rightarrow \mathbb{R}$ is continuous, show that $F(y) = \int^b_a f(x,y) dx$ is continuous.
lean statement:

codex statement:
theorem continuous_of_continuous_integral:
  fixes f::"'a::metric_space \<Rightarrow> 'b::metric_space \<Rightarrow> 'c::metric_space"
  assumes "continuous_on (UNIV::'a set) (\<lambda>y. ∫ {a..b} (f x y) dx)"
  shows "continuous_on (UNIV::'b set) (\<lambda>y. ∫ {a..b} (f x y) dx)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_22: undefined oops


(*
problem_number:5_43a
natural language statement:
Suppose that $T \colon R^n \rightarrow R^m$ has rank $k$.  Show there exists a $\delta > 0$ such that if $S \colon R^n \rightarrow R^m$ and $||S - T|| < \delta$ then $S$ has rank $\geq k$.
lean statement:

codex statement:
theorem exists_delta_of_rank_leq_rank_of_norm_lt_delta:
  fixes T::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and S::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear T" "linear S" "rank T = k"
  shows "\<exists>δ>0. \<forall>S. linear S \<longrightarrow> (∥S - T∥ < δ \<longrightarrow> rank S \<ge> k)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_43a: undefined oops


(*
problem_number:6_38
natural language statement:
If $f$ and $g$ are integrable prove that their maximum and minimum are integrable.
lean statement:

codex statement:
theorem integrable_max_min:
  fixes f g::"'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>x. max (f x) (g x))" "integrable M (\<lambda>x. min (f x) (g x))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_38: undefined oops


(*
problem_number:6_39
natural language statement:
Suppose that $f$ and $g$ are measurable and their squares are integrable. Prove that $fg$ is measurable, integrable, and $\int fg \leq \sqrt{\int f^2} \sqrt{\int g^2}$.
lean statement:

codex statement:
theorem integrable_of_integrable_square:
  fixes f g::"'a::euclidean_space \<Rightarrow> real"
  assumes "integrable lborel f" "integrable lborel g"
  shows "integrable lborel (\<lambda>x. f x * g x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_39: undefined oops


(*
problem_number:6_43
natural language statement:
Prove that $g(y) = \int_0^\infty e^{-x} \sin(x + y) dx$ is differentiable and find $g'(y)$.
lean statement:

codex statement:
theorem diff_integral_of_exp_sin:
  fixes y::real
  shows "((\<lambda>x. exp (-x) * sin (x + y)) has_vector_derivative (exp (-y) * cos y)) (at y)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_43: undefined oops


(*
problem_number:6_49a
natural language statement:
Prove that $f \colon \mathbb{R} \rightarrow \mathbb{R}$ is Lebesgue measurable if and only if the preimage of every Borel set is a Lebesgue measurable.
lean statement:

codex statement:
theorem lebesgue_measurable_of_preimage_borel_is_lebesgue_measurable:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "\<forall>s. borel_measurable s \<longrightarrow> borel_measurable (f -` s)"
  shows "lebesgue_measurable f"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_49a: undefined oops




end
