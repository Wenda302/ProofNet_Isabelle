theory Rudin
 imports Main
begin

(*
problem_number:1_1a
natural language statement:
If $r$ is rational $(r \neq 0)$ and $x$ is irrational, prove that $r+x$ is irrational.
lean statement:
theorem exercise_1_1a
  (x : ℝ) (y : ℚ) :
  ( irrational x ) -> irrational ( x + y ) :=
begin
  apply irrational.add_rat,
end

codex statement:
theorem irrational_of_add_irrational_rational:
  fixes r::real and x::real
  assumes "r ≠ 0" "irrational x"
  shows "irrational (r + x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1a: undefined oops


(*
problem_number:1_1b
natural language statement:
If $r$ is rational $(r \neq 0)$ and $x$ is irrational, prove that $rx$ is irrational.
lean statement:
theorem exercise_1_1b
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( irrational x ) -> irrational ( x * y ) :=
begin
  intro g,
  apply irrational.mul_rat g h,
end

codex statement:
theorem irrational_of_rational_times_irrational:
  fixes r::real and x::real
  assumes "r ≠ 0" "irrational x" "rational r"
  shows "irrational (r*x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1b: undefined oops


(*
problem_number:1_2
natural language statement:
Prove that there is no rational number whose square is $12$.
lean statement:
theorem exercise_1_2
: ¬ ∃ (x : ℚ), ( x ^ 2 = 12 ) :=

codex statement:
theorem no_rational_square_eq_12:
  assumes "∃x. x^2 = 12"
  shows "False"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_2: undefined oops


(*
problem_number:1_4
natural language statement:
Let $E$ be a nonempty subset of an ordered set; suppose $\alpha$ is a lower bound of $E$ and $\beta$ is an upper bound of $E$. Prove that $\alpha \leq \beta$.
lean statement:
theorem exercise_1_4
(α : Type* ) [partial_order α]
(s : set α)
(x y : α)
(h₀ : set.nonempty s)
(h₁ : x ∈ lower_bounds s)
(h₂ : y ∈ upper_bounds s)
: x ≤ y :=
begin
  have h : ∃ z, z ∈ s := h₀,
  cases h with z,
  have xlez : x ≤ z :=
  begin
  apply h₁,
  assumption,
  end,
  have zley : z ≤ y :=
  begin
  apply h₂,
  assumption,
  end,
  exact xlez.trans zley,
end

codex statement:
theorem lower_bound_leq_upper_bound:
  fixes E::"'a::linorder set"
  assumes "E ≠ {}" "∀x∈E. α ≤ x" "∀x∈E. x ≤ β"
  shows "α ≤ β"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_4: undefined oops


(*
problem_number:1_5
natural language statement:
Let $A$ be a nonempty set of real numbers which is bounded below. Let $-A$ be the set of all numbers $-x$, where $x \in A$. Prove that $\inf A=-\sup (-A)$.
lean statement:
theorem exercise_1_5
  (A minus_A : set ℝ) (hA : A.nonempty) (hA_bdd_below : bdd_below A)
  (hminus_A : minus_A = {x | -x ∈ A}) :
  Inf A = Sup minus_A :=

codex statement:
theorem inf_of_neg_sup_of_neg:
  fixes A::"real set"
  assumes "bdd_below A" "A ≠ {}"
  shows "Inf A = - Sup (-A)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_5: undefined oops


(*
problem_number:1_8
natural language statement:
Prove that no order can be defined in the complex field that turns it into an ordered field. Hint: $-1$ is a square.
lean statement:
theorem exercise_1_8
  : ¬ ∃ (r : ℂ → ℂ → Prop), is_linear_order ℂ r :=

codex statement:
theorem no_order_in_complex_field:
  fixes z::complex
  assumes "∀x y. x ≤ y ⟶ x + z ≤ y + z" "∀x y. x ≤ y ⟶ x * z ≤ y * z" "∀x. x ≤ x" "∀x y. x ≤ y ⟶ y ≤ x ⟶ x = y" "∀x y z. x ≤ y ⟶ x + z ≤ y + z" "∀x y. x ≤ y ⟶ x * y ≤ y * x" "∀x y z. x ≤ y ⟶ x * (y + z) ≤ x * y + x * z" "∃x. x < x"
  shows False
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_8: undefined oops


(*
problem_number:1_8
natural language statement:
Prove that $|\mathbf{x}+\mathbf{y}|^{2}+|\mathbf{x}-\mathbf{y}|^{2}=2|\mathbf{x}|^{2}+2|\mathbf{y}|^{2}$ if $\mathbf{x} \in R^{k}$ and $\mathbf{y} \in R^{k}$.
lean statement:
theorem exercise_1_8
  : ¬ ∃ (r : ℂ → ℂ → Prop), is_linear_order ℂ r :=

codex statement:
theorem sum_add_square_sub_square_eq_sum_square:
  fixes x y::"'a::euclidean_space"
  shows "norm (x+y)^2 + norm (x - y) ^ 2 = 2 * (norm x)^2 + 2* (norm y)^2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_8: undefined oops


(*
problem_number:1_14
natural language statement:
If $z$ is a complex number such that $|z|=1$, that is, such that $z \bar{z}=1$, compute $|1+z|^{2}+|1-z|^{2}$.
lean statement:
theorem exercise_1_14
  (z : ℂ) (h : abs z = 1)
  : (abs (1 + z)) ^ 2 + (abs (1 - z)) ^ 2 = 4 :=

codex statement:
theorem sum_square_of_sum_sub_of_abs_eq_one:
  fixes z::complex
  assumes "norm z = 1"
  shows "norm (1 + z)^2 + norm (1 - z)^2 = 4"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_14: undefined oops


(*
problem_number:1_18a
natural language statement:
If $k \geq 2$ and $\mathbf{x} \in R^{k}$, prove that there exists $\mathbf{y} \in R^{k}$ such that $\mathbf{y} \neq 0$ but $\mathbf{x} \cdot \mathbf{y}=0$
lean statement:
theorem exercise_1_18a
  (n : ℕ)
  (h : n > 1)
  (x : euclidean_space ℝ (fin n)) -- R^n
  : ∃ (y : euclidean_space ℝ (fin n)), y ≠ 0 ∧ (inner x y) = (0 : ℝ) :=

codex statement:
theorem exists_nonzero_orthogonal_vector:
  fixes x::"'a::euclidean_space"
  assumes "k≥2"
  shows "∃y. y ≠ 0 ∧ x ⋅ y = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_18a: undefined oops


(*
problem_number:1_25
natural language statement:
25: Prove that every compact metric space $K$ has a countable base.
lean statement:

codex statement:
theorem compact_metric_space_has_countable_base:
  fixes K::"'a::metric_space set"
  assumes "compact K"
  shows "countable (UNIV::'a set)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_25: undefined oops


(*
problem_number:1_27a
natural language statement:
27a: Suppose $E\subset\mathbb{R}^k$ is uncountable, and let $P$ be the set of condensation points of $E$. Prove that $P$ is perfect.
lean statement:

codex statement:
theorem perfect_of_uncountable_condensation_points:
  fixes E::"'a::euclidean_space set"
  assumes "uncountable E" "P = condensation_points E"
  shows "perfect P"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_27a: undefined oops


(*
problem_number:1_27b
natural language statement:
27b: Suppose $E\subset\mathbb{R}^k$ is uncountable, and let $P$ be the set of condensation points of $E$. Prove that at most countably many point of $E$ are not in $P$.
lean statement:

codex statement:
theorem countable_of_uncountable_set_of_condensation_points:
  fixes E::"'a::euclidean_space set"
  assumes "uncountable E"
  shows "countable {x∈E. x∉condensation_points E}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_27b: undefined oops


(*
problem_number:1_28
natural language statement:
Prove that every closed set in a separable metric space is the union of a (possibly empty) perfect set and a set which is at most countable.
lean statement:

codex statement:
theorem closed_set_union_perfect_set_countable_set:
  fixes X::"'a::metric_space set"
  assumes "separable X" "closed X"
  shows "∃P C. perfect P ∧ countable C ∧ X = P ∪ C"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_28: undefined oops


(*
problem_number:1_29
natural language statement:
Prove that every open set in $\mathbb{R}$ is the union of an at most countable collection of disjoint segments.
lean statement:

codex statement:
theorem open_set_union_of_countable_disjoint_segments:
  fixes A::"real set"
  assumes "open A"
  shows "∃f. countable (f ` (UNIV::nat set)) ∧ pairwise disjoint (f ` (UNIV::nat set)) ∧ (⋃i∈UNIV. f i) = A"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_29: undefined oops


(*
problem_number:2_19a
natural language statement:
If $A$ and $B$ are disjoint closed sets in some metric space $X$, prove that they are separated.
lean statement:
theorem exercise_2_19a {X : Type*} [metric_space X]
  (A B : set X) (hA : is_closed A) (hB : is_closed B) (hAB : disjoint A B) :
  separated_nhds A B :=

codex statement:
theorem separated_of_disjoint_closed:
  fixes A B::"'a::metric_space set"
  assumes "closed A" "closed B" "A ∩ B = {}"
  shows "separated A B"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_19a: undefined oops


(*
problem_number:2_24
natural language statement:
Let $X$ be a metric space in which every infinite subset has a limit point. Prove that $X$ is separable. Hint: Fix $\delta>0$, and pick $x_{1} \in X$. Having chosen $x_{1}, \ldots, x_{J} \in X$,
lean statement:
theorem exercise_2_24 {X : Type*} [metric_space X]
  (hX : ∀ (A : set X), infinite A → ∃ (x : X), x ∈ closure A) :
  separable_space X :=

codex statement:
theorem separable_of_infinite_subset_has_limit_point:
  fixes X::"'a::metric_space set"
  assumes "∀A. infinite A ⟶ ∃x∈A. ∀ε>0. ∃y∈A. y≠x ∧ dist x y < ε"
  shows "separable X"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_24: undefined oops


(*
problem_number:3_1a
natural language statement:
Prove that convergence of $\left\{s_{n}\right\}$ implies convergence of $\left\{\left|s_{n}\right|\right\}$.
lean statement:
theorem exercise_3_1a
  (f : ℕ → ℝ)
  (h : ∃ (a : ℝ), tendsto (λ (n : ℕ), f n) at_top (𝓝 a))
  : ∃ (a : ℝ), tendsto (λ (n : ℕ), |f n|) at_top (𝓝 a) :=
begin
  cases h with a h,
  use |a|,
  apply filter.tendsto.abs h,
end

codex statement:
theorem convergent_of_convergent_abs:
  fixes s::"nat ⇒ 'a::real_normed_vector"
  assumes "convergent s"
  shows "convergent (λn. norm (s n))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_1a: undefined oops


(*
problem_number:3_3
natural language statement:
If $s_{1}=\sqrt{2}$, and $s_{n+1}=\sqrt{2+\sqrt{s_{n}}} \quad(n=1,2,3, \ldots),$ prove that $\left\{s_{n}\right\}$ converges, and that $s_{n}<2$ for $n=1,2,3, \ldots$.
lean statement:
theorem exercise_3_3
  : ∃ (x : ℝ), tendsto f at_top (𝓝 x) ∧ ∀ n, f n < 2 :=

codex statement:
theorem sqrt_2_lt_2_of_sqrt_2_plus_sqrt_s_n:
  fixes s::"nat ⇒ real"
  assumes "s 1 = sqrt 2" "∀n. s (n+1) = sqrt (2 + sqrt (s n))"
  shows "∀n. s n < 2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_3: undefined oops


(*
problem_number:3_5
natural language statement:
For any two real sequences $\left\{a_{n}\right\},\left\{b_{n}\right\}$, prove that $\limsup _{n \rightarrow \infty}\left(a_{n}+b_{n}\right) \leq \limsup _{n \rightarrow \infty} a_{n}+\limsup _{n \rightarrow \infty} b_{n},$ provided the sum on the right is not of the form $\infty-\infty$.
lean statement:
theorem exercise_3_5 -- TODO fix
  (a b : ℕ → ℝ)
  (h : limsup a + limsup b ≠ 0) :
  limsup (λ n, a n + b n) ≤ limsup a + limsup b :=

codex statement:
theorem limsup_sum_leq_sum_limsup:
  fixes a b::"nat ⇒ real"
  assumes "∀n. a n ≤ b n"
  shows "limsup (λn. a n + b n) ≤ limsup a + limsup b"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_5: undefined oops


(*
problem_number:3_7
natural language statement:
Prove that the convergence of $\Sigma a_{n}$ implies the convergence of $\sum \frac{\sqrt{a_{n}}}{n}$ if $a_n\geq 0$.
lean statement:
theorem exercise_3_7
  (a : ℕ → ℝ)
  (h : ∃ y, (tendsto (λ n, (∑ i in (finset.range n), a i)) at_top (𝓝 y))) :
  ∃ y, tendsto (λ n, (∑ i in (finset.range n), sqrt (a i) / n)) at_top (𝓝 y) :=

codex statement:
theorem sum_sqrt_div_n_converges_of_sum_converges:
  fixes a::"nat ⇒ real"
  assumes "summable a" "∀n. a n ≥ 0"
  shows "summable (λn. sqrt (a n) / n)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_7: undefined oops


(*
problem_number:3_8
natural language statement:
If $\Sigma a_{n}$ converges, and if $\left\{b_{n}\right\}$ is monotonic and bounded, prove that $\Sigma a_{n} b_{n}$ converges.
lean statement:
theorem exercise_3_8
  (a b : ℕ → ℝ)
  (h1 : ∃ y, (tendsto (λ n, (∑ i in (finset.range n), a i)) at_top (𝓝 y)))
  (h2 : monotone b)
  (h3 : metric.bounded (set.range b)) :
  ∃ y, tendsto (λ n, (∑ i in (finset.range n), (a i) * (b i))) at_top (𝓝 y) :=

codex statement:
theorem convergent_of_convergent_and_monotonic_bounded:
  fixes a::"nat ⇒ real" and b::"nat ⇒ real"
  assumes "convergent a" "bounded (range b)" "mono b"
  shows "convergent (λn. a n * b n)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_8: undefined oops


(*
problem_number:3_13
natural language statement:
Prove that the Cauchy product of two absolutely convergent series converges absolutely.
lean statement:
theorem exercise_3_13
  (a b : ℕ → ℝ)
  (ha : ∃ y, (tendsto (λ n, (∑ i in (finset.range n), |a i|)) at_top (𝓝 y)))
  (hb : ∃ y, (tendsto (λ n, (∑ i in (finset.range n), |b i|)) at_top (𝓝 y))) :
  ∃ y, (tendsto (λ n, (∑ i in (finset.range n),
  λ i, (∑ j in finset.range (i + 1), a j * b (i - j)))) at_top (𝓝 y)) :=

codex statement:
theorem abs_convergent_of_cauchy_product:
  fixes f g::"nat ⇒ 'a::real_normed_algebra_1"
  assumes "summable (λn. abs (f n))" "summable (λn. abs (g n))"
  shows "summable (λn. abs (∑i<n. f i * g (n - i)))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_13: undefined oops


(*
problem_number:3_20
natural language statement:
Suppose $\left\{p_{n}\right\}$ is a Cauchy sequence in a metric space $X$, and some sequence $\left\{p_{n l}\right\}$ converges to a point $p \in X$. Prove that the full sequence $\left\{p_{n}\right\}$ converges to $p$.
lean statement:
theorem exercise_3_20 {X : Type*} [metric_space X]
  (p : ℕ → X) (l : ℕ) (r : X)
  (hp : cauchy_seq p)
  (hpl : tendsto (λ n, p (l * n)) at_top (𝓝 r)) :
  tendsto p at_top (𝓝 r) :=

codex statement:
theorem convergent_of_subseq_convergent:
  fixes X::"'a::metric_space" and p::"'a" and pn::"nat ⇒ 'a"
  assumes "Cauchy pn" "convergent (λn. pn (n l))" "∀n. pn (n l) ⟶ p"
  shows "pn ⟶ p"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_20: undefined oops


(*
problem_number:3_21
natural language statement:
If $\left\{E_{n}\right\}$ is a sequence of closed nonempty and bounded sets in a complete metric space $X$, if $E_{n} \supset E_{n+1}$, and if $\lim _{n \rightarrow \infty} \operatorname{diam} E_{n}=0,$ then $\bigcap_{1}^{\infty} E_{n}$ consists of exactly one point.
lean statement:
theorem exercise_3_21
  {X : Type*} [metric_space X] [complete_space X]
  (E : ℕ → set X)
  (hE : ∀ n, E n ⊃ E (n + 1))
  (hE' : tendsto (λ n, metric.diam (E n)) at_top (𝓝 0)) :
  ∃ a, set.Inter E = {a} :=

codex statement:
theorem singleton_of_closed_nonempty_bounded_diam_zero:
  fixes X::"'a::metric_space set"
  assumes "∀n. closed (E n)" "∀n. E n ≠ {}" "∀n. bounded (E n)" "∀n. E n ⊆ E (n+1)" "diameter (E n) ⟶ 0"
  shows "∃x. (∩n. E n) = {x}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_21: undefined oops


(*
problem_number:3_22
natural language statement:
Suppose $X$ is a nonempty complete metric space, and $\left\{G_{n}\right\}$ is a sequence of dense open sets of $X$. Prove Baire's theorem, namely, that $\bigcap_{1}^{\infty} G_{n}$ is not empty.
lean statement:
theorem exercise_3_22 (X : Type* ) [metric_space X] [complete_space X]
  (G : ℕ → set X) (hG : ∀ n, is_open (G n) ∧ dense (G n)) :
  ∃ x, ∀ n, x ∈ G n :=

codex statement:
theorem baire_theorem:
  fixes X::"'a::metric_space set" and G::"'a set set"
  assumes "complete_space X" "∀n. openin (subtopology X UNIV) (G n)" "∀n. dense_in (subtopology X UNIV) (G n)"
  shows "∃x. ∀n. x∈G n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_22: undefined oops


(*
problem_number:4_2a
natural language statement:
If $f$ is a continuous mapping of a metric space $X$ into a metric space $Y$, prove that $f(\overline{E}) \subset \overline{f(E)}$ for every set $E \subset X$. ($\overline{E}$ denotes the closure of $E$).
lean statement:
theorem exercise_4_2a
  {α : Type} [metric_space α]
  {β : Type} [metric_space β]
  (f : α → β)
  (h₁ : continuous f)
  : ∀ (x : set α), f '' (closure x) ⊆ closure (f '' x) :=
begin
  intros X x h₂ Y h₃,
  simp at *,
  cases h₃ with h₃ h₄,
  cases h₂ with w h₅,
  cases h₅ with h₅ h₆,
  have h₈ : is_closed (f ⁻¹' Y) := is_closed.preimage h₁ h₃,
  have h₉ : closure X ⊆ f ⁻¹' Y := closure_minimal h₄ h₈,
  rw ←h₆,
  exact h₉ h₅,
end

codex statement:
theorem closure_of_continuous_image_subset_continuous_image_closure:
  fixes f::"'a::metric_space ⇒ 'b::metric_space" and E::"'a set"
  assumes "continuous_on UNIV f"
  shows "closure (f ` E) ⊆ f ` closure E"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_2a: undefined oops


(*
problem_number:4_3
natural language statement:
Let $f$ be a continuous real function on a metric space $X$. Let $Z(f)$ (the zero set of $f$ ) be the set of all $p \in X$ at which $f(p)=0$. Prove that $Z(f)$ is closed.
lean statement:
theorem exercise_4_3
  {α : Type} [metric_space α]
  (f : α → ℝ) (h : continuous f) (z : set α) (g : z = f⁻¹' {0})
  : is_closed z :=
begin
  rw g,
  apply is_closed.preimage h,
  exact is_closed_singleton,
end

codex statement:
theorem zero_set_of_continuous_is_closed:
  fixes f::"'a::metric_space ⇒ real"
  assumes "continuous_on UNIV f"
  shows "closed {x∈UNIV. f x = 0}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_3: undefined oops


(*
problem_number:4_4a
natural language statement:
Let $f$ and $g$ be continuous mappings of a metric space $X$ into a metric space $Y$, and let $E$ be a dense subset of $X$. Prove that $f(E)$ is dense in $f(X)$.
lean statement:
theorem exercise_4_4a
  {α : Type} [metric_space α]
  {β : Type} [metric_space β]
  (f : α → β)
  (s : set α)
  (h₁ : continuous f)
  (h₂ : dense s)
  : f '' set.univ ⊆ closure (f '' s) :=
begin
  simp,
  exact continuous.range_subset_closure_image_dense h₁ h₂,
end

codex statement:
theorem dense_of_continuous_dense:
  fixes f::"'a::metric_space ⇒ 'b::metric_space" and g::"'a::metric_space ⇒ 'b::metric_space"
  assumes "continuous_on UNIV f" "continuous_on UNIV g" "dense (f ` UNIV)" "dense (g ` UNIV)"
  shows "dense ((f ∘ g) ` UNIV)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_4a: undefined oops


(*
problem_number:4_5a
natural language statement:
If $f$ is a real continuous function defined on a closed set $E \subset R^{1}$, prove that there exist continuous real functions $g$ on $R^{1}$ such that $g(x)=f(x)$ for all $x \in E$.
lean statement:
theorem exercise_4_5a
  (f : ℝ → ℝ)
  (E : set ℝ)
  (h₁ : is_closed E)
  (h₂ : continuous_on f E)
  : ∃ (g : ℝ → ℝ), continuous g ∧ ∀ x ∈ E, f x = g x :=

codex statement:
theorem exists_continuous_extension:
  fixes f::"real ⇒ real" and E::"real set"
  assumes "continuous_on E f" "closed E"
  shows "∃g. continuous_on UNIV g ∧ (∀x∈E. g x = f x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5a: undefined oops


(*
problem_number:4_6
natural language statement:
If $f$ is defined on $E$, the graph of $f$ is the set of points $(x, f(x))$, for $x \in E$. In particular, if $E$ is a set of real numbers, and $f$ is real-valued, the graph of $f$ is a subset of the plane. Suppose $E$ is compact, and prove that $f$ is continuous on $E$ if and only if its graph is compact.
lean statement:
theorem exercise_4_6
  (f : ℝ → ℝ)
  (E : set ℝ)
  (G : set (ℝ × ℝ))
  (h₁ : is_compact E)
  (h₂ : G = {(x, f x) | x ∈ E})
  : continuous_on f E ↔ is_compact G :=

codex statement:
theorem compact_of_continuous_graph:
  fixes f::"'a::metric_space ⇒ 'b::metric_space" and E::"'a::metric_space set"
  assumes "compact E" "continuous_on E f"
  shows "compact {(x, f x) | x. x ∈ E}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_6: undefined oops


(*
problem_number:4_8a
natural language statement:
Let $f$ be a real uniformly continuous function on the bounded set $E$ in $R^{1}$. Prove that $f$ is bounded on $E$.
lean statement:
theorem exercise_4_8a
  (E : set ℝ) (f : ℝ → ℝ) (hf : uniform_continuous_on f E)
  (hE : metric.bounded E) : metric.bounded (set.image f E) :=

codex statement:
theorem bounded_of_uniformly_continuous_on_bounded:
  fixes f::"'a::metric_space ⇒ 'b::real_normed_vector"
  assumes "bounded (UNIV::'a set)" "uniformly_continuous_on UNIV f"
  shows "bounded (range f)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_8a: undefined oops


(*
problem_number:4_11a
natural language statement:
Suppose $f$ is a uniformly continuous mapping of a metric space $X$ into a metric space $Y$ and prove that $\left\{f\left(x_{n}\right)\right\}$ is a Cauchy sequence in
lean statement:
theorem exercise_4_11a
  {X : Type*} [metric_space X]
  {Y : Type*} [metric_space Y]
  (f : X → Y) (hf : uniform_continuous f)
  (x : ℕ → X) (hx : cauchy_seq x) :
  cauchy_seq (λ n, f (x n)) :=

codex statement:
theorem cauchy_of_uniform_continuous:
  fixes f::"'a::metric_space ⇒ 'b::metric_space"
  assumes "uniformly_continuous_on UNIV f" "cauchy (f ∘ g)"
  shows "cauchy g"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_11a: undefined oops


(*
problem_number:4_12
natural language statement:
A uniformly continuous function of a uniformly continuous function is uniformly continuous.
lean statement:
theorem exercise_4_12
  {α β γ : Type*} [uniform_space α] [uniform_space β] [uniform_space γ]
  {f : α → β} {g : β → γ}
  (hf : uniform_continuous f) (hg : uniform_continuous g) :
  uniform_continuous (g ∘ f) :=

codex statement:
theorem uniform_continuous_of_uniform_continuous_comp:
  fixes f::"'a::metric_space ⇒ 'b::metric_space" and g::"'b::metric_space ⇒ 'c::metric_space"
  assumes "uniformly_continuous_on UNIV f" "uniformly_continuous_on UNIV g"
  shows "uniformly_continuous_on UNIV (g ∘ f)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_12: undefined oops


(*
problem_number:4_14
natural language statement:
Let $I=[0,1]$ be the closed unit interval. Suppose $f$ is a continuous mapping of $I$ into $I$. Prove that $f(x)=x$ for at least one $x \in I$.
lean statement:
theorem exercise_4_14 [topological_space I]
  [linear_order I] (f : I → I) (hf : continuous f) :
  ∃ (x : I), f x = x :=

codex statement:
theorem exists_fixed_point_of_continuous_on_closed_interval:
  fixes f::"real ⇒ real"
  assumes "continuous_on {0..1} f"
  shows "∃x. x∈{0..1} ∧ f x = x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_14: undefined oops


(*
problem_number:4_15
natural language statement:
Prove that every continuous open mapping of $R^{1}$ into $R^{1}$ is monotonic.
lean statement:
theorem exercise_4_15 {f : ℝ → ℝ}
  (hf : continuous f) (hof : is_open_map f) :
  monotone f :=

codex statement:
theorem monotonic_of_continuous_open_mapping:
  fixes f::"real ⇒ real"
  assumes "continuous_on UNIV f" "open_mapping f"
  shows "mono f"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_15: undefined oops


(*
problem_number:4_19
natural language statement:
Suppose $f$ is a real function with domain $R^{1}$ which has the intermediate value property. If $f(a)<c<f(b)$, then $f(x)=c$ for some $x$ between $a$ and $b$. Suppose also, for every rational $r$, that the set of all $x$ with $f(x)=r$ is closed. Prove that $f$ is continuous.
lean statement:
theorem exercise_4_19
  {f : ℝ → ℝ} (hf : ∀ a b c, a < b → f a < c → c < f b → ∃ x, a < x ∧ x < b ∧ f x = c)
  (hg : ∀ r : ℚ, is_closed {x | f x = r}) : continuous f :=

codex statement:
theorem continuous_of_intermediate_value_property_and_closed_set_of_rational_value:
  fixes f::"real ⇒ real"
  assumes "∀a b c. a < b ⟶ f a < c ⟶ c < f b ⟶ ∃x. a < x ⟶ x < b ⟶ f x = c"
    "∀r. closed {x | x ∈ UNIV ∧ f x = r}"
  shows "continuous_on UNIV f"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_19: undefined oops


(*
problem_number:4_21a
natural language statement:
Suppose $K$ and $F$ are disjoint sets in a metric space $X, K$ is compact, $F$ is closed. Prove that there exists $\delta>0$ such that $d(p, q)>\delta$ if $p \in K, q \in F$.
lean statement:
theorem exercise_4_21a {X : Type*} [metric_space X]
  (K F : set X) (hK : is_compact K) (hF : is_closed F) (hKF : disjoint K F) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (p q : X), p ∈ K → q ∈ F → dist p q ≥ δ :=

codex statement:
theorem exists_delta_of_disjoint_compact_closed:
  fixes K F::"'a::metric_space set"
  assumes "compact K" "closed F" "K ∩ F = {}"
  shows "∃δ>0. ∀p∈K. ∀q∈F. dist p q > δ"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_21a: undefined oops


(*
problem_number:4_24
natural language statement:
Assume that $f$ is a continuous real function defined in $(a, b)$ such that $f\left(\frac{x+y}{2}\right) \leq \frac{f(x)+f(y)}{2}$ for all $x, y \in(a, b)$. Prove that $f$ is convex.
lean statement:
theorem exercise_4_24 {f : ℝ → ℝ}
  (hf : continuous f) (a b : ℝ) (hab : a < b)
  (h : ∀ x y : ℝ, a < x → x < b → a < y → y < b → f ((x + y) / 2) ≤ (f x + f y) / 2) :
  convex_on ℝ (set.Ioo a b) f :=

codex statement:
theorem convex_of_continuous_and_ineq:
  fixes f::"real ⇒ real"
  assumes "continuous_on {a<..<b} f" "∀x y. x ∈ {a<..<b} ⟶ y ∈ {a<..<b} ⟶ f ((x + y) / 2) ≤ (f x + f y) / 2"
  shows "convex_on {a<..<b} f"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_24: undefined oops


(*
problem_number:4_26a
natural language statement:
Suppose $X, Y, Z$ are metric spaces, and $Y$ is compact. Let $f$ map $X$ into $Y$, let $g$ be a continuous one-to-one mapping of $Y$ into $Z$, and put $h(x)=g(f(x))$ for $x \in X$. Prove that $f$ is uniformly continuous if $h$ is uniformly continuous.
lean statement:

codex statement:
theorem uniform_continuous_of_continuous_injective_uniform_continuous_comp:
  fixes f::"'a::metric_space ⇒ 'b::metric_space" and g::"'b::metric_space ⇒ 'c::metric_space"
  assumes "compact (UNIV::'b set)" "continuous_on UNIV g" "inj g" "uniformly_continuous_on UNIV (g ∘ f)"
  shows "uniformly_continuous_on UNIV f"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_26a: undefined oops


(*
problem_number:5_1
natural language statement:
Let $f$ be defined for all real $x$, and suppose that $|f(x)-f(y)| \leq(x-y)^{2}$for all real $x$ and $y$. Prove that $f$ is constant.
lean statement:
theorem exercise_5_1
  {f : ℝ → ℝ} (hf : ∀ x y : ℝ, | (f x - f y) | ≤ (x - y) ^ 2) :
  ∃ c, f = λ x, c :=

codex statement:
theorem constant_of_diff_leq_square_diff:
  fixes f::"real ⇒ real"
  assumes "∀x y. abs (f x - f y) ≤ (x - y)^2"
  shows "f constant_on UNIV"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_1: undefined oops


(*
problem_number:5_2
natural language statement:
Suppose $f^{\prime}(x)>0$ in $(a, b)$. Prove that $f$ is strictly increasing in $(a, b)$, and let $g$ be its inverse function. Prove that $g$ is differentiable, and that$g^{\prime}(f(x))=\frac{1}{f^{\prime}(x)} \quad(a<x<b)$
lean statement:
theorem exercise_5_2 {a b : ℝ}
  {f g : ℝ → ℝ} (hf : ∀ x ∈ set.Ioo a b, deriv f x > 0)
  (hg : g = f⁻¹)
  (hg_diff : differentiable_on ℝ g (set.Ioo a b)) :
  differentiable_on ℝ g (set.Ioo a b) ∧
  ∀ x ∈ set.Ioo a b, deriv g x = 1 / deriv f x :=

codex statement:
theorem derivative_of_inverse_function:
  fixes f::"real ⇒ real" and g::"real ⇒ real"
  assumes "a < b" "continuous_on {a..b} f" "∀x∈{a..b}. f differentiable (at x)" "∀x∈{a..b}. 0 < f' x"
  shows "∀x∈{a..b}. g differentiable (at x)" "∀x∈{a..b}. g' x = 1 / f' (g x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_2: undefined oops


(*
problem_number:5_3
natural language statement:
Suppose $g$ is a real function on $R^{1}$, with bounded derivative (say $\left|g^{\prime}\right| \leq M$ ). Fix $\varepsilon>0$, and define $f(x)=x+\varepsilon g(x)$. Prove that $f$ is one-to-one if $\varepsilon$ is small enough.
lean statement:
theorem exercise_5_3 {g : ℝ → ℝ} (hg : continuous g)
  (hg' : ∃ M : ℝ, ∀ x : ℝ, | deriv g x | ≤ M) :
  ∃ N, ∀ ε > 0, ε < N → function.injective (λ x : ℝ, x + ε * g x) :=

codex statement:
theorem injective_of_small_epsilon:
  fixes g::"real ⇒ real"
  assumes "∀x. abs (g' x) ≤ M"
  shows "∃ε>0. ∀x y. abs (x - y) < ε ⟶ g x ≠ g y"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_3: undefined oops


(*
problem_number:5_4
natural language statement:
If $C_{0}+\frac{C_{1}}{2}+\cdots+\frac{C_{n-1}}{n}+\frac{C_{n}}{n+1}=0,$ where $C_{0}, \ldots, C_{n}$ are real constants, prove that the equation $C_{0}+C_{1} x+\cdots+C_{n-1} x^{n-1}+C_{n} x^{n}=0$ has at least one real root between 0 and 1 .
lean statement:
theorem exercise_5_4 {n : ℕ}
  (C : ℕ → ℝ)
  (hC : ∑ i in (finset.range (n + 1)), (C i) / (i + 1) = 0) :
  ∃ x, x ∈ (set.Icc (0 : ℝ) 1) ∧ ∑ i in finset.range (n + 1), (C i) * (x^i) = 0 :=

codex statement:
theorem exists_real_root_of_polynomial_of_sum_eq_zero:
  fixes C::"real ⇒ real"
  assumes "∀n. C n = 0" "∑n. C n / (n+1) = 0"
  shows "∃x. 0 < x ∧ x < 1 ∧ (∑n. C n * x^n) = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_4: undefined oops


(*
problem_number:5_5
natural language statement:
Suppose $f$ is defined and differentiable for every $x>0$, and $f^{\prime}(x) \rightarrow 0$ as $x \rightarrow+\infty$. Put $g(x)=f(x+1)-f(x)$. Prove that $g(x) \rightarrow 0$ as $x \rightarrow+\infty$.
lean statement:
theorem exercise_5_5
  {f : ℝ → ℝ}
  (hfd : differentiable ℝ f)
  (hf : tendsto (deriv f) at_top (𝓝 0)) :
  tendsto (λ x, f (x + 1) - f x) at_top at_top :=

codex statement:
theorem tendsto_zero_of_tendsto_zero_derivative:
  fixes f::"real ⇒ real"
  assumes "∀x. 0 < x ⟶ f differentiable (at x)" "((λx. f' x) ---> 0) at_top"
  shows "((λx. f (x + 1) - f x) ---> 0) at_top"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_5: undefined oops


(*
problem_number:5_6
natural language statement:
Suppose (a) $f$ is continuous for $x \geq 0$, (b) $f^{\prime}(x)$ exists for $x>0$, (c) $f(0)=0$, (d) $f^{\prime}$ is monotonically increasing. Put $g(x)=\frac{f(x)}{x} \quad(x>0)$ and prove that $g$ is monotonically increasing.
lean statement:
theorem exercise_5_6
  {f : ℝ → ℝ}
  (hf1 : continuous f)
  (hf2 : ∀ x, differentiable_at ℝ f x)
  (hf3 : f 0 = 0)
  (hf4 : monotone (deriv f)) :
  monotone_on (λ x, f x / x) (set.Ioi 0) :=

codex statement:
theorem monotone_increasing_of_continuous_derivative_monotone_increasing:
  fixes f::"real ⇒ real"
  assumes "continuous_on {0..} f" "∀x>0. (f has_real_derivative f' x) (at x)" "f 0 = 0" "mono f'"
  shows "mono (λx. f x / x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_6: undefined oops


(*
problem_number:5_7
natural language statement:
Suppose $f^{\prime}(x), g^{\prime}(x)$ exist, $g^{\prime}(x) \neq 0$, and $f(x)=g(x)=0$. Prove that $\lim _{t \rightarrow x} \frac{f(t)}{g(t)}=\frac{f^{\prime}(x)}{g^{\prime}(x)}.$
lean statement:
theorem exercise_5_7
  {f g : ℝ → ℝ} {x : ℝ}
  (hf' : differentiable_at ℝ f 0)
  (hg' : differentiable_at ℝ g 0)
  (hg'_ne_0 : deriv g 0 ≠ 0)
  (f0 : f 0 = 0) (g0 : g 0 = 0) :
  tendsto (λ x, f x / g x) (𝓝 x) (𝓝 (deriv f x / deriv g x)) :=

codex statement:
theorem lim_frac_of_derivative_eq_derivative_frac:
  fixes f g::"real ⇒ real"
  assumes "f differentiable (at x)" "g differentiable (at x)" "g x ≠ 0" "f x = g x = 0"
  shows "(f has_real_derivative (f' x)) (at x)" "(g has_real_derivative (g' x)) (at x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_7: undefined oops


(*
problem_number:5_15
natural language statement:
Suppose $a \in R^{1}, f$ is a twice-differentiable real function on $(a, \infty)$, and $M_{0}, M_{1}, M_{2}$ are the least upper bounds of $|f(x)|,\left|f^{\prime}(x)\right|,\left|f^{\prime \prime}(x)\right|$, respectively, on $(a, \infty)$. Prove that $M_{1}^{2} \leq 4 M_{0} M_{2} .$
lean statement:
theorem exercise_5_15 {f : ℝ → ℝ} (a M0 M1 M2 : ℝ)
  (hf' : differentiable_on ℝ f (set.Ici a))
  (hf'' : differentiable_on ℝ (deriv f) (set.Ici a))
  (hM0 : M0 = Sup {(| f x | )| x ∈ (set.Ici a)})
  (hM1 : M1 = Sup {(| deriv f x | )| x ∈ (set.Ici a)})
  (hM2 : M2 = Sup {(| deriv (deriv f) x | )| x ∈ (set.Ici a)}) :
  (M1 ^ 2) ≤ 4 * M0 * M2 :=

codex statement:

Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_15: undefined oops


(*
problem_number:5_17
natural language statement:
Suppose $f$ is a real, three times differentiable function on $[-1,1]$, such that $f(-1)=0, \quad f(0)=0, \quad f(1)=1, \quad f^{\prime}(0)=0 .$ Prove that $f^{(3)}(x) \geq 3$ for some $x \in(-1,1)$.
lean statement:
theorem exercise_5_17
  {f : ℝ → ℝ}
  (hf' : differentiable_on ℝ f (set.Icc (-1) 1))
  (hf'' : differentiable_on ℝ (deriv f) (set.Icc 1 1))
  (hf''' : differentiable_on ℝ (deriv (deriv f)) (set.Icc 1 1))
  (hf0 : f (-1) = 0)
  (hf1 : f 0 = 0)
  (hf2 : f 1 = 1)
  (hf3 : deriv f 0 = 0) :
  ∃ x, x ∈ set.Ioo (-1 : ℝ) 1 ∧ deriv (deriv (deriv f)) x ≥ 3 :=

codex statement:
theorem exists_x_in_interval_of_three_times_differentiable_function:
  fixes f::"real ⇒ real"
  assumes "∀x. f differentiable (at x)" "∀x. f differentiable (at x within {-1..1})" "∀x. f differentiable (at x within {-1..1})" "f (-1) = 0" "f 0 = 0" "f 1 = 1" "f' 0 = 0"
  shows "∃x∈{-1..1}. f''' x ≥ 3"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_17: undefined oops


(*
problem_number:6_1
natural language statement:
Suppose $\alpha$ increases on $[a, b], a \leq x_{0} \leq b, \alpha$ is continuous at $x_{0}, f\left(x_{0}\right)=1$, and $f(x)=0$ if $x \neq x_{0}$. Prove that $f \in \mathcal{R}(\alpha)$ and that $\int f d \alpha=0$.
lean statement:

codex statement:
theorem integral_of_continuous_function_eq_zero:
  fixes f::"real ⇒ real" and α::"real ⇒ real"
  assumes "a ≤ x₀" "x₀ ≤ b" "continuous (at x₀) α" "f x₀ = 1" "f x = 0" "∀x. a ≤ x ∧ x ≤ b ⟶ α x ≤ α x₀"
  shows "f ∈ borel_measurable α" "integral α f = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_1: undefined oops


(*
problem_number:6_2
natural language statement:
Suppose $f \geq 0, f$ is continuous on $[a, b]$, and $\int_{a}^{b} f(x) d x=0$. Prove that $f(x)=0$ for all $x \in[a, b]$.
lean statement:

codex statement:
theorem zero_integral_of_continuous_nonneg_implies_zero_function:
  fixes f::"real ⇒ real"
  assumes "continuous_on {a..b} f" "f ≥ 0" "integral {a..b} f = 0"
  shows "∀x∈{a..b}. f x = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_2: undefined oops


(*
problem_number:6_4
natural language statement:
If $f(x)=0$ for all irrational $x, f(x)=1$ for all rational $x$, prove that $f \notin \mathcal{R}$ on $[a, b]$ for any $a<b$.
lean statement:

codex statement:
theorem not_Riemann_integrable_of_zero_for_irrational_one_for_rational:
  fixes f::"real ⇒ real"
  assumes "∀x. irrational x ⟶ f x = 0" "∀x. rational x ⟶ f x = 1"
  shows "∀a b. a < b ⟶ ¬ (f integrable_on {a..b})"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_4: undefined oops


(*
problem_number:6_6
natural language statement:
Let $P$ be the Cantor set. Let $f$ be a bounded real function on $[0,1]$ which is continuous at every point outside $P$. Prove that $f \in \mathcal{R}$ on $[0,1]$.
lean statement:

codex statement:
theorem R_of_bounded_continuous_at_outside_Cantor:
  fixes f::"real ⇒ real"
  assumes "bounded (range f)" "∀x∈{0..1} - cantor. continuous (at x) f"
  shows "f ∈ R {0..1}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_6: undefined oops




end