theory Shakarchi
 imports Main
begin

(*
problem_number:1_13a
natural language statement:
Suppose that $f$ is holomorphic in an open set $\Omega$. Prove that if $\text{Re}(f)$ is constant, then $f$ is constant.
lean statement:
theorem exercise_1_13a {f : ℂ → ℂ} (Ω : set ℂ) (a b : Ω) (h : is_open Ω)
  (hf : differentiable_on ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).re = c) :
  f a = f b :=

codex statement:
theorem holomorphic_const_of_real_const:
  fixes f::"complex ⇒ complex"
  assumes "open s" "f holomorphic_on s" "∀x∈s. Re (f x) = c"
  shows "∀x∈s. f x = c"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_13a: undefined oops


(*
problem_number:1_13b
natural language statement:
Suppose that $f$ is holomorphic in an open set $\Omega$. Prove that if $\text{Im}(f)$ is constant, then $f$ is constant.
lean statement:
theorem exercise_1_13b {f : ℂ → ℂ} (Ω : set ℂ) (a b : Ω) (h : is_open Ω)
  (hf : differentiable_on ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).im = c) :
  f a = f b :=

codex statement:
theorem constant_of_holomorphic_constant_imag:
  fixes f::"complex ⇒ complex"
  assumes "open s" "f holomorphic_on s" "∀x∈s. Im (f x) = c"
  shows "∀x∈s. f x = c"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_13b: undefined oops


(*
problem_number:1_13c
natural language statement:
Suppose that $f$ is holomorphic in an open set $\Omega$. Prove that if $|f|$ is constant, then $f$ is constant.
lean statement:
theorem exercise_1_13c {f : ℂ → ℂ} (Ω : set ℂ) (a b : Ω) (h : is_open Ω)
  (hf : differentiable_on ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, abs (f z) = c) :
  f a = f b :=

codex statement:
theorem holomorphic_constant_of_constant_abs:
  fixes f::"complex ⇒ complex"
  assumes "open s" "f holomorphic_on s" "∀x∈s. f x ≠ 0" "∀x y. x ∈ s ⟶ y ∈ s ⟶ norm (f x) = norm (f y)"
  shows "∀x y. x ∈ s ⟶ y ∈ s ⟶ f x = f y"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_13c: undefined oops


(*
problem_number:1_18
natural language statement:
Let $f$ be a power series centered at the origin. Prove that $f$ has a power series expansion around any point in its disc of convergence.
lean statement:

codex statement:
theorem power_series_expansion_of_power_series_centered_at_origin:
  fixes f::"complex ⇒ complex"
  assumes "∀x. f x = (∑n. f n * x^n)" "∃r. ∀x. norm x < r ⟶ f x = (∑n. f n * x^n)"
  shows "∀z. ∃r. ∀x. norm (x - z) < r ⟶ f x = (∑n. f n * (x - z)^n)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_18: undefined oops


(*
problem_number:1_19a
natural language statement:
Prove that the power series $\sum nz^n$ does not converge on any point of the unit circle.
lean statement:
theorem exercise_1_19a (z : ℂ) (hz : abs z = 1) (s : ℕ → ℂ)
    (h : s = (λ n, ∑ i in (finset.range n), i * z ^ i)) :
    ¬ ∃ y, tendsto s at_top (𝓝 y) :=

codex statement:
theorem power_series_not_converges_on_unit_circle:
  fixes z::complex
  assumes "norm z = 1"
  shows "∀ε>0. ∃N. ∀n≥N. norm (of_nat n * z^n) ≥ ε"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_19a: undefined oops


(*
problem_number:1_19b
natural language statement:
Prove that the power series $\sum zn/n^2$ converges at every point of the unit circle.
lean statement:
theorem exercise_1_19b (z : ℂ) (hz : abs z = 1) (s : ℕ → ℂ)
    (h : s = (λ n, ∑ i in (finset.range n), i * z / i ^ 2)) :
    ∃ y, tendsto s at_top (𝓝 y) :=

codex statement:
theorem converges_power_series_of_unit_circle:
  fixes z::complex
  assumes "norm z = 1"
  shows "summable (λn. z^n / n^2)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_19b: undefined oops


(*
problem_number:1_19c
natural language statement:
Prove that the power series $\sum zn/n$ converges at every point of the unit circle except $z = 1$.
lean statement:
theorem exercise_1_19c (z : ℂ) (hz : abs z = 1) (hz2 : z ≠ 1) (s : ℕ → ℂ)
    (h : s = (λ n, ∑ i in (finset.range n), i * z / i)) :
    ∃ z, tendsto s at_top (𝓝 z) :=

codex statement:
theorem power_series_converges_at_every_point_of_unit_circle_except_z_eq_1:
  fixes z::complex
  assumes "norm z = 1" "z ≠ 1"
  shows "summable (λn. z^n / of_nat n)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_19c: undefined oops


(*
problem_number:1_22
natural language statement:
Let $\mathbb{N} = {1, 2, 3, \ldots}$ denote the set of positive integers. A subset $S \subset \mathbb{N}$ is said to be in arithmetic progression if $S = {a, a + d, a + 2d, a + 3d, \ldots}$ where $a, d \in \mathbb{N}$. Here $d$ is called the step of $S$.  Show that $\mathbb{N}$ cannot be partitioned into a finite number of subsets that are in arithmetic progression with distinct steps (except for the trivial case $a = d = 1$).
lean statement:
theorem exercise_1_22 (n : ℕ) (S : fin n → set ℕ) (f : fin n → ℕ × ℕ)
  (h : ∀ i, S i = set.range (λ j, (f i).fst + j * (f i).snd)) :
    ¬ (⋃ i, S i) = (set.univ : set ℕ) :=

codex statement:
theorem not_finite_partition_of_nat_into_arithmetic_progression:
  fixes S::"nat set"
  assumes "finite S" "∀s∈S. ∃a d. s = {a, a + d, a + 2*d, a + 3*d, a + 4*d, a + 5*d, a + 6*d, a + 7*d, a + 8*d, a + 9*d}"
  shows "∃s∈S. s = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_22: undefined oops


(*
problem_number:1_26
natural language statement:
Suppose $f$ is continuous in a region $\Omega$. Prove that any two primitives of $f$ (if they exist) differ by a constant.
lean statement:
theorem exercise_1_26
  (f F₁ F₂ : ℂ → ℂ) (Ω : set ℂ) (h1 : is_open Ω) (h2 : is_connected Ω)
  (hF₁ : differentiable_on ℂ F₁ Ω) (hF₂ : differentiable_on ℂ F₂ Ω)
  (hdF₁ : ∀ x ∈ Ω, deriv F₁ x = f x) (hdF₂ : ∀ x ∈ Ω, deriv F₂ x = f x)
  : ∃ c : ℂ, ∀ x, F₁ x = F₂ x + c :=

codex statement:
theorem primitives_diff_const:
  fixes f::"'a::euclidean_space ⇒ 'b::real_normed_vector"
  assumes "continuous_on Ω f" "∃g. (∀x∈Ω. (f x) = (vector_derivative g (at x) within Ω))" "∃h. (∀x∈Ω. (f x) = (vector_derivative h (at x) within Ω))"
  shows "∃c. (∀x∈Ω. g x = h x + c)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_26: undefined oops


(*
problem_number:2_2
natural language statement:
Show that $\int_{0}^{\infty} \frac{\sin x}{x} d x=\frac{\pi}{2}$.
lean statement:
theorem exercise_2_2 :
  tendsto (λ y, ∫ x in 0..y, real.sin x / x) at_top (𝓝 (real.pi / 2)) :=

codex statement:
theorem integral_sin_x_over_x_eq_pi_div_2:
  fixes f::"real ⇒ real"
  assumes "f integrable_on {0..∞}" "∀x. 0 ≤ x ⟶ f x = sin x / x"
  shows "integral {0..∞} f = pi / 2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_2: undefined oops


(*
problem_number:2_5
natural language statement:
Suppose $f$ is continuously complex differentiable on $\Omega$, and $T \subset \Omega$ is a triangle whose interior is also contained in $\Omega$. Apply Green’s theorem to show that $\int_T f(z) dz = 0$.
lean statement:

codex statement:
theorem integral_of_complex_differentiable_on_triangle_eq_zero:
  fixes f::"complex ⇒ complex" and T::"complex set"
  assumes "continuous_on T f" "f complex_differentiable_on T" "∃a b c. T = convex hull {a, b, c}"
  shows "∫ T f = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_5: undefined oops


(*
problem_number:2_6
natural language statement:
Let $\Omega$ be an open subset of $\mathbb{C}$ and let $T \subset \Omega$ be a triangle whose interior is also contained in $\Omega$. Suppose that $f$ is a function holomorphic in $\Omega$ except possibly at a point w inside $T$. Prove that if $f$ is bounded near $w$, then $\int_T f(z) dz = 0$.
lean statement:

codex statement:
theorem integral_of_holomorphic_eq_zero_of_bounded_near_point:
  fixes f::"complex ⇒ complex" and T::"complex set"
  assumes "open Ω" "T ⊆ Ω" "interior T ⊆ Ω" "f holomorphic_on (Ω - {w})" "bounded (f ` (ball w r))"
  shows "∫ T f = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_6: undefined oops


(*
problem_number:2_9
natural language statement:
Let $\Omega$ be a bounded open subset of $\mathbb{C}$, and $\varphi: \Omega \rightarrow \Omega$ a holomorphic function. Prove that if there exists a point $z_{0} \in \Omega$ such that $\varphi\left(z_{0}\right)=z_{0} \quad \text { and } \quad \varphi^{\prime}\left(z_{0}\right)=1$ then $\varphi$ is linear.
lean statement:
theorem exercise_2_9
  {f : ℂ → ℂ} (Ω : set ℂ) (b : metric.bounded Ω) (h : is_open Ω)
  (hf : differentiable_on ℂ f Ω) (z ∈ Ω) (hz : f z = z) (h'z : deriv f z = 1) :
  ∃ (f_lin : ℂ →L[ℂ] ℂ), ∀ x ∈ Ω, f x = f_lin x :=

codex statement:
theorem linear_of_holomorphic_and_derivative_one:
  fixes f::"complex ⇒ complex"
  assumes "open s" "bounded s" "f holomorphic_on s" "z∈s" "f z = z" "deriv f z = 1"
  shows "∀w∈s. f w = w + (z - w)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_9: undefined oops


(*
problem_number:2_13
natural language statement:
Suppose $f$ is an analytic function defined everywhere in $\mathbb{C}$ and such that for each $z_0 \in \mathbb{C}$ at least one coefficient in the expansion $f(z) = \sum_{n=0}^\infty c_n(z - z_0)^n$ is equal to 0. Prove that $f$ is a polynomial.
lean statement:
theorem exercise_2_13 {f : ℂ → ℂ}
    (hf : ∀ z₀ : ℂ, ∃ (s : set ℂ) (c : ℕ → ℂ), is_open s ∧ z₀ ∈ s ∧
      ∀ z ∈ s, tendsto (λ n, ∑ i in finset.range n, (c i) * (z - z₀)^i) at_top (𝓝 (f z₀))
      ∧ ∃ i, c i = 0) :
    ∃ (c : ℕ → ℂ) (n : ℕ), f = λ z, ∑ i in finset.range n, (c i) * z ^ n :=

codex statement:
theorem is_polynomial_of_analytic_and_coeff_zero:
  fixes f::"complex ⇒ complex"
  assumes "∀z. analytic f (at z)" "∀z. ∃n. c n z = 0"
  shows "∃p. ∀z. f z = p z"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_13: undefined oops


(*
problem_number:3_2
natural language statement:
Evaluate the integral $\int_{-\infty}^{\infty} \frac{dx}{1 + x^4}$.
lean statement:
theorem exercise_3_22 (D : set ℂ) (hD : D = ball 0 1) (f : ℂ → ℂ)
    (hf : differentiable_on ℂ f D) (hfc : continuous_on f (closure D)) :
    ¬ ∀ z ∈ (sphere (0 : ℂ) 1), f z = 1 / z :=

codex statement:
theorem integral_of_inverse_of_one_plus_x_four:
  fixes f::"real ⇒ real"
  assumes "finite (set_integrable lborel {-∞..∞} f)"
  shows "(∫₋∞ ∞ (λx. 1/(1+x^4)) dx) = (∫₋∞ ∞ f dx)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_2: undefined oops


(*
problem_number:3_3
natural language statement:
Show that $ \int_{-\infty}^{\infty} \frac{\cos x}{x^2 + a^2} dx = \pi \frac{e^{-a}}{a}$ for $a > 0$.
lean statement:
theorem exercise_3_3 (a : ℝ) (ha : 0 < a) :
    tendsto (λ y, ∫ x in -y..y, real.cos x / (x ^ 2 + a ^ 2))
      at_top (𝓝 (real.pi * (real.exp (-a) / a))) :=

codex statement:
theorem integral_cos_over_square_plus_a_square_eq_pi_exp_minus_a_over_a:
  fixes a::real
  assumes "a > 0"
  shows "∫ {-∞..∞} (λx. cos x / (x^2 + a^2)) = π * exp (-a) / a"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_3: undefined oops


(*
problem_number:3_4
natural language statement:
Show that $ \int_{-\infty}^{\infty} \frac{x \sin x}{x^2 + a^2} dx = \pi e^{-a}$ for $a > 0$.
lean statement:
theorem exercise_3_4 (a : ℝ) (ha : 0 < a) :
    tendsto (λ y, ∫ x in -y..y, x * real.sin x / (x ^ 2 + a ^ 2))
      at_top (𝓝 (real.pi * (real.exp (-a)))) :=

codex statement:
theorem integral_sin_over_square_plus_a_square_eq_pi_exp_minus_a:
  fixes a::real
  assumes "a>0"
  shows "(∫ x = -∞..∞. (x * sin x) / (x^2 + a^2)) = π * exp (-a)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_4: undefined oops


(*
problem_number:3_9
natural language statement:
Show that $\int_0^1 \log(\sin \pi x) dx = - \log 2$.
lean statement:
theorem exercise_3_9 : ∫ x in 0..1, real.log (real.sin (real.pi * x)) = - real.log 2 :=
  
codex statement:
theorem integral_log_sin_pi_x_eq_log_2:
  fixes f::"real ⇒ real"
  assumes "f integrable_on {0..1}" "f = (λx. log (sin (π * x)))"
  shows "(∫ {0..1} f) = - log 2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_9: undefined oops


(*
problem_number:3_14
natural language statement:
Prove that all entire functions that are also injective take the form $f(z) = az + b$, $a, b \in \mathbb{C}$ and $a \neq 0$.
lean statement:
theorem exercise_3_14 {f : ℂ → ℂ} (hf : differentiable ℂ f)
    (hf_inj : function.injective f) :
    ∃ (a b : ℂ), f = (λ z, a * z + b) ∧ a ≠ 0 :=

codex statement:
theorem entire_injective_eq_linear:
  fixes f::"complex ⇒ complex"
  assumes "entire f" "inj f"
  shows "∃a b. f = (λz. a * z + b)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_14: undefined oops


(*
problem_number:3_22
natural language statement:
Show that there is no holomorphic function $f$ in the unit disc $D$ that extends continuously to $\partial D$ such that $f(z) = 1/z$ for $z \in \partial D$.
lean statement:
theorem exercise_3_22 (D : set ℂ) (hD : D = ball 0 1) (f : ℂ → ℂ)
    (hf : differentiable_on ℂ f D) (hfc : continuous_on f (closure D)) :
    ¬ ∀ z ∈ (sphere (0 : ℂ) 1), f z = 1 / z :=

codex statement:
theorem no_holomorphic_function_extends_continuously_to_boundary_of_unit_disc:
  fixes f::"complex ⇒ complex"
  assumes "continuous_on (cball 0 1) f" "f holomorphic_on ball 0 1" "∀z∈cball 0 1. z ≠ 0 ⟶ f z = 1/z"
  shows False
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_22: undefined oops


(*
problem_number:4_4a
natural language statement:
Suppose $Q$ is a polynomial of degree $\geq 2$ with distinct roots, none lying on the real axis. Calculate $\int_{-\infty}^\infty \frac{e^{-2 \pi ix \xi}}{Q(x)} dx$, $\xi \in \mathbb{R}$, in terms of the roots of $Q$.
lean statement:

codex statement:
theorem integral_of_polynomial_of_degree_geq_2_with_distinct_roots:
  fixes Q::"complex ⇒ complex"
  assumes "degree Q ≥ 2" "∀x. Q x ≠ 0" "∀x. ∃y. Q x = y^2"
  shows "∫ {-∞..∞} (λx. exp (-2 * π * complex_of_real x * ξ) / Q x) dx = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_4a: undefined oops


(*
problem_number:5_1
natural language statement:
Prove that if $f$ is holomorphic in the unit disc, bounded and not identically zero, and $z_{1}, z_{2}, \ldots, z_{n}, \ldots$ are its zeros $\left(\left|z_{k}\right|<1\right)$, then $\sum_{n}\left(1-\left|z_{n}\right|\right)<\infty$.
lean statement:
theorem exercise_5_1 (f : ℂ → ℂ) (hf : differentiable_on ℂ f (ball 0 1))
  (hb : bounded (set.range f)) (h0 : f ≠ 0) (zeros : ℕ → ℂ) (hz : ∀ n, f (zeros n) = 0)
  (hzz : set.range zeros = {z | f z = 0 ∧ z ∈ (ball (0 : ℂ) 1)}) :
  ∃ (z : ℂ), tendsto (λ n, (∑ i in finset.range n, (1 - zeros i))) at_top (𝓝 z) :=

codex statement:
theorem sum_of_one_minus_abs_of_zeros_of_holomorphic_bounded_not_identically_zero_is_finite:
  fixes f::"complex ⇒ complex"
  assumes "∀z. f holomorphic (at z)" "bounded (range f)" "∀z. f z ≠ 0" "∀n. ∃z. f z = 0 ∧ norm z < 1"
  shows "finite {z. f z = 0 ∧ norm z < 1}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_1: undefined oops


(*
problem_number:5_3
natural language statement:
Show that $\sum \frac{z^{n}}{(n !)^{\alpha}}$ is an entire function of order $1 / \alpha$.
lean statement:

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_3: undefined oops




end