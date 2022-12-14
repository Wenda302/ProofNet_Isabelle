theory "Ireland-Rosen"
 imports Main
begin

(*
problem_number:1_27
natural language statement:
For all odd $n$ show that $8 \mid n^{2}-1$.
lean statement:
theorem exercise_1_27 {n : ℕ} (hn : odd n) : 8 ∣ (n^2 - 1) :=

codex statement:
theorem div_8_of_odd_n:
  fixes n::nat
  assumes "odd n"
  shows "8 ∣ n^2 - 1"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_27: undefined oops


(*
problem_number:1_30
natural language statement:
Prove that $\frac{1}{2}+\frac{1}{3}+\cdots+\frac{1}{n}$ is not an integer.
lean statement:
theorem exercise_1_30 {n : ℕ} : 
  ¬ ∃ a : ℤ, ∑ (i : fin n), (1 : ℚ) / (n+2) = a :=

codex statement:
theorem sum_frac_not_integer:
  fixes n::nat
  shows "∑i<n. 1 / real i ≠ int (∑i<n. 1 / real i)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_30: undefined oops


(*
problem_number:1_31
natural language statement:
Show that 2 is divisible by $(1+i)^{2}$ in $\mathbb{Z}[i]$.
lean statement:
theorem exercise_1_31  : (⟨1, 1⟩ : gaussian_int) ^ 2 ∣ 2 := 

codex statement:
theorem divisible_of_power_of_one_plus_i:
  fixes z::complex
  assumes "z ∈ {x + y * \<i> |x y. x ∈ UNIV ∧ y ∈ UNIV}"
  shows "∃a. 2 = (1 + \<i>)^2 * a"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_31: undefined oops


(*
problem_number:2_4
natural language statement:
If $a$ is a nonzero integer, then for $n>m$ show that $\left(a^{2^{n}}+1, a^{2^{m}}+1\right)=1$ or 2 depending on whether $a$ is odd or even.
lean statement:
theorem exercise_2_4 {a : ℤ} (ha : a ≠ 0) 
  (f_a := λ n m : ℕ, int.gcd (a^(2^n) + 1) (a^(2^m)+1)) {n m : ℕ} 
  (hnm : n > m) : 
  (odd a → f_a n m = 1) ∧ (even a → f_a n m = 2) :=

codex statement:
theorem gcd_of_power_of_two_plus_one_eq_one_or_two:
  fixes a::int
  assumes "a ≠ 0" "n > m"
  shows "gcd (a^(2^n) + 1) (a^(2^m) + 1) = 1 ∨ gcd (a^(2^n) + 1) (a^(2^m) + 1) = 2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_4: undefined oops


(*
problem_number:2_21
natural language statement:
Define $\wedge(n)=\log p$ if $n$ is a power of $p$ and zero otherwise. Prove that $\sum_{A \mid n} \mu(n / d) \log d$ $=\wedge(n)$.
lean statement:
theorem exercise_2_21 {l : ℕ → ℝ} 
  (hl : ∀ p n : ℕ, p.prime → l (p^n) = log p )
  (hl1 : ∀ m : ℕ, ¬ is_prime_pow m → l m = 0) :
  l = λ n, ∑ d : divisors n, moebius (n/d) * log d  := 

codex statement:
theorem sum_mu_log_divisors_eq_log_prime_power:
  fixes n::nat
  assumes "∃p. prime p ∧ n = p^a"
  shows "(∑d∣n. μ (n div d) * log d) = log p"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_21: undefined oops


(*
problem_number:2_27a
natural language statement:
Show that $\sum^{\prime} 1 / n$, the sum being over square free integers, diverges.
lean statement:
theorem exercise_2_27a : 
  ¬ summable (λ i : {p : ℤ // squarefree p}, (1 : ℚ) / i) :=

codex statement:
theorem diverges_sum_of_inverse_square_free_integers:
  fixes n::nat
  shows "∑i=1..n. 1 / (real_of_nat i) = ∞"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_27a: undefined oops


(*
problem_number:3_1
natural language statement:
Show that there are infinitely many primes congruent to $-1$ modulo 6 .
lean statement:
theorem exercise_3_1 : infinite {p : primes // p ≡ -1 [ZMOD 6]} :=

codex statement:
theorem infinite_primes_congruent_minus_one_mod_six:
  shows "infinite {p::nat. prime p ∧ p ≡ -1 [MOD 6]}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_1: undefined oops


(*
problem_number:3_4
natural language statement:
Show that the equation $3 x^{2}+2=y^{2}$ has no solution in integers.
lean statement:
theorem exercise_3_4 : ¬ ∃ x y : ℤ, 3*x^2 + 2 = y^2 :=

codex statement:
theorem no_solution_of_3_x_square_plus_2_eq_y_square:
  fixes x y::int
  assumes "3 * x^2 + 2 = y^2"
  shows "False"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_4: undefined oops


(*
problem_number:3_5
natural language statement:
Show that the equation $7 x^{3}+2=y^{3}$ has no solution in integers.
lean statement:
theorem exercise_3_5 : ¬ ∃ x y : ℤ, 7*x^3 + 2 = y^3 :=

codex statement:
theorem no_solution_of_eq_7_x_cube_plus_2_eq_y_cube:
  assumes "∃x y. 7 * x^3 + 2 = y^3"
  shows False
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_5: undefined oops


(*
problem_number:3_10
natural language statement:
If $n$ is not a prime, show that $(n-1) ! \equiv 0(n)$, except when $n=4$.
lean statement:
theorem exercise_3_10 {n : ℕ} (hn0 : ¬ n.prime) (hn1 : n ≠ 4) : 
  factorial (n-1) ≡ 0 [MOD n] :=

codex statement:
theorem fact_minus_one_equiv_zero_of_not_prime:
  fixes n::nat
  assumes "n>2" "∀p. prime p ⟶ p ∣ n ⟶ p = 2 ∨ p = n"
  shows "(fact (n - 1)) mod n = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_10: undefined oops


(*
problem_number:3_14
natural language statement:
Let $p$ and $q$ be distinct odd primes such that $p-1$ divides $q-1$. If $(n, p q)=1$, show that $n^{q-1} \equiv 1(p q)$.
lean statement:
theorem exercise_3_14 {p q n : ℕ} (hp0 : p.prime ∧ p > 2) 
  (hq0 : q.prime ∧ q > 2) (hpq0 : p ≠ q) (hpq1 : p - 1 ∣ q - 1)
  (hn : n.gcd (p*q) = 1) : 
  n^(q-1) ≡ 1 [MOD p*q] :=

codex statement:
theorem congruent_one_of_prime_diff_one_divides_prime_diff_one:
  fixes p q n::nat
  assumes "prime p" "prime q" "p ≠ q" "p - 1 ∣ q - 1" "coprime n (p * q)"
  shows "n [^] (q - 1) ≡ 1 (mod p * q)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_14: undefined oops


(*
problem_number:3_18
natural language statement:
Let $N$ be the number of solutions to $f(x) \equiv 0(n)$ and $N_{i}$ be the number of solutions to $f(x) \equiv 0\left(p_{i}^{a_{i}}\right)$. Prove that $N=N_{1} N_{2} \cdots N_{i}$.
lean statement:

codex statement:
theorem number_of_solutions_of_congruence_eq_product_of_number_of_solutions_of_congruence_mod_prime_power:
  fixes f::"nat ⇒ nat" and n::nat
  assumes "∀p. prime p ⟶ ∃a. p^a ∣ n"
  shows "∃N. ∀p. prime p ⟶ ∃a. p^a ∣ n ⟶ (∃Np. ∀x. f x ≡ 0 [MOD p^a] ⟶ (∃!x. f x ≡ 0 [MOD p^a])) ⟶ (∃Np. ∀x. f x ≡ 0 [MOD n] ⟶ (∃!x. f x ≡ 0 [MOD n]))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_18: undefined oops


(*
problem_number:3_20
natural language statement:
Show that $x^{2} \equiv 1\left(2^{b}\right)$ has one solution if $b=1$, two solutions if $b=2$, and four solutions if $b \geq 3$.
lean statement:

codex statement:
theorem number_of_solutions_of_x_square_equiv_1_mod_2_power_b:
  fixes b::nat
  assumes "b≥1"
  shows "card {x::int. x^2 ≡ 1 [MOD 2^b]} = 2^(b-1)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_20: undefined oops


(*
problem_number:4_4
natural language statement:
Consider a prime $p$ of the form $4 t+1$. Show that $a$ is a primitive root modulo $p$ iff - $a$ is a primitive root modulo $p$.
lean statement:
theorem exercise_4_4 {p t: ℕ} (hp0 : p.prime) (hp1 : p = 4*t + 1) 
  (a : zmod p): 
  is_primitive_root a p ↔ is_primitive_root (-a) p :=

codex statement:
theorem primitive_root_of_prime_of_form_4_t_1:
  fixes p::nat and a::int
  assumes "prime p" "p = 4 * t + 1" "coprime a p"
  shows "∃n. a [^] n ≡ -1 [mod p]"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_4: undefined oops


(*
problem_number:4_5
natural language statement:
Consider a prime $p$ of the form $4 t+3$. Show that $a$ is a primitive root modulo $p$ iff $-a$ has order $(p-1) / 2$.
lean statement:

codex statement:
theorem primitive_root_iff_order_half_minus_a:
  fixes p::nat and a::int
  assumes "prime p" "p ≡ 3 (mod 4)"
  shows "∃b. order b p = (p - 1) div 2 ⟷ primitive_root a p"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5: undefined oops


(*
problem_number:4_6
natural language statement:
If $p=2^{n}+1$ is a Fermat prime, show that 3 is a primitive root modulo $p$.
lean statement:

codex statement:
theorem primitive_root_of_fermat_prime:
  fixes p::nat
  assumes "prime p" "∃n. p = 2^n + 1"
  shows "∃m. ∀k. coprime k p ⟶ (3::nat) [^] k ≡ 1 [^] m [MOD p]"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_6: undefined oops


(*
problem_number:4_8
natural language statement:
Let $p$ be an odd prime. Show that $a$ is a primitive root module $p$ iff $a^{(p-1) / q} \not \equiv 1(p)$ for all prime divisors $q$ of $p-1$.
lean statement:

codex statement:
theorem primitive_root_of_prime_iff_not_cong_one_of_prime_divisor:
  fixes p::nat and a::int
  assumes "prime p" "odd p"
  shows "∀q. prime q ∧ q dvd p - 1 ⟶ a [^] ((p - 1) div q) ≡ 1 (mod p) ⟷ ¬ primitive_root p a"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_8: undefined oops


(*
problem_number:4_9
natural language statement:
Show that the product of all the primitive roots modulo $p$ is congruent to $(-1)^{\phi(p-1)}$ modulo $p$.
lean statement:

codex statement:
theorem prod_primitive_roots_eq_pow_phi_minus_one_mod_p:
  fixes p::nat
  assumes "prime p"
  shows "(∏x∈primitive_roots p. x) ≡ (-1) ^ (φ p - 1) [MOD p]"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_9: undefined oops


(*
problem_number:4_10
natural language statement:
Show that the sum of all the primitive roots modulo $p$ is congruent to $\mu(p-1)$ modulo $p$.
lean statement:

codex statement:
theorem sum_primitive_roots_eq_mu_p_minus_one:
  fixes p::nat
  assumes "prime p"
  shows "(∑x∈{x. x < p ∧ coprime x p ∧ ∃n. x [^] n ≡ 1 [MOD p]}. x) ≡ μ (p - 1) [MOD p]"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_10: undefined oops


(*
problem_number:4_11
natural language statement:
Prove that $1^{k}+2^{k}+\cdots+(p-1)^{k} \equiv 0(p)$ if $p-1 \nmid k$ and $-1(p)$ if $p-1 \mid k$.
lean statement:

codex statement:
theorem sum_of_powers_cong_zero_mod_p_of_p_minus_one_not_dvd_k:
  fixes p::nat and k::int
  assumes "prime p" "p-1 ≠ 0" "p-1 ∣ k"
  shows "(∑i<p-1. i^k) ≡ -1 (mod p)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_11: undefined oops


(*
problem_number:4_22
natural language statement:
If $a$ has order 3 modulo $p$, show that $1+a$ has order 6 .
lean statement:

codex statement:
theorem order_of_one_plus_a_eq_6_of_order_a_eq_3:
  fixes a::nat and p::nat
  assumes "prime p" "a mod p ≠ 0" "∀n. a [^] n mod p ≠ 1 ⟶ n ≥ 3"
  shows "∀n. (1 + a) [^] n mod p ≠ 1 ⟶ n ≥ 6"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_22: undefined oops


(*
problem_number:4_24
natural language statement:
Show that $a x^{m}+b y^{n} \equiv c(p)$ has the same number of solutions as $a x^{m^{\prime}}+b y^{n^{\prime}} \equiv c(p)$, where $m^{\prime}=(m, p-1)$ and $n^{\prime}=(n, p-1)$.
lean statement:

codex statement:
theorem number_of_solutions_of_congruence_eq_number_of_solutions_of_congruence_of_coprime_powers:
  fixes a b c::"int" and m n m' n'::nat
  assumes "prime p" "coprime m (p - 1)" "coprime n (p - 1)" "m' = gcd m (p - 1)" "n' = gcd n (p - 1)"
  shows "card {(x, y). x < p ∧ y < p ∧ a * x ^ m + b * y ^ n ≡ c (mod p)} = card {(x, y). x < p ∧ y < p ∧ a * x ^ m' + b * y ^ n' ≡ c (mod p)}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_24: undefined oops


(*
problem_number:5_2
natural language statement:
Show that the number of solutions to $x^{2} \equiv a(p)$ is given by $1+(a / p)$.
lean statement:
theorem exercise_5_28 {p : ℕ} (hp : p.prime) (hp1 : p ≡ 1 [MOD 4]): 
  ∃ x, x^4 ≡ 2 [MOD p] ↔ ∃ A B, p = A^2 + 64*B^2 :=

codex statement:
theorem number_of_solutions_of_congruence_eq_one_plus_a_div_p:
  fixes a p::nat
  assumes "prime p"
  shows "card {x. x^2 ≡ a [MOD p]} = 1 + (a div p)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_2: undefined oops


(*
problem_number:5_3
natural language statement:
Suppose that $p \nmid a$. Show that the number of solutions to $a x^{2}+b x+c \equiv 0(p)$ is given by $1+\left(\left(b^{2}-4 a c\right) / p\right)$.
lean statement:
theorem exercise_5_37 {p q : ℕ} [fact(p.prime)] [fact(q.prime)] {a : ℤ}
  (ha : a < 0) (h0 : p ≡ q [ZMOD 4*a]) (h1 : ¬ ((p : ℤ) ∣ a)) :
  legendre_sym p a = legendre_sym q a :=

codex statement:
theorem number_of_solutions_of_quadratic_congruence_eq_1_plus_Legendre_symbol:
  fixes a b c p::nat
  assumes "prime p" "coprime a p"
  shows "card {x. x < p ∧ (a * x^2 + b * x + c) ≡ 0 [MOD p]} = 1 + (Legendre_symbol (a * b^2 - 4 * a * c) p)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_3: undefined oops


(*
problem_number:5_4
natural language statement:
Prove that $\sum_{a=1}^{p-1}(a / p)=0$.
lean statement:

codex statement:
theorem sum_of_p_minus_one_eq_zero:
  fixes p::nat
  assumes "prime p"
  shows "(∑a=1..p-1. a / p) = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_4: undefined oops


(*
problem_number:5_5
natural language statement:
Prove that $\sum_{\substack{p-1 \\ x=0}}((a x+b) / p)=0$ provided that $p \nmid a .$
lean statement:

codex statement:
theorem sum_of_arithmetic_progression_eq_zero_of_coprime:
  fixes a b p::nat
  assumes "coprime a p"
  shows "(∑x=0..p-1. (a * x + b) / p) = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_5: undefined oops


(*
problem_number:5_6
natural language statement:
Show that the number of solutions to $x^{2}-y^{2} \equiv a(p)$ is given by $\sum_{y=0}^{p-1}\left(1+\left(\left(y^{2}+a\right) / p\right)\right) .$
lean statement:

codex statement:
theorem sum_of_solutions_of_congruence_eq_sum_of_legendre_symbol:
  fixes p::nat and a::int
  assumes "prime p"
  shows "card {x. x^2 ≡ a [MOD p]} = (∑y<p. 1 + legendre_symbol (y^2 + a) p)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_6: undefined oops


(*
problem_number:5_7
natural language statement:
By calculating directly show that the number of solutions to $x^{2}-y^{2} \equiv a(p)$ is $p-1$ if $p \nmid a$ and $2 p-1$ if $p \mid a$.
lean statement:

codex statement:
theorem number_of_solutions_of_congruence_eq_p_minus_one_if_p_not_dvd_a:
  fixes p::nat and a::int
  assumes "prime p" "p ∣ a"
  shows "card {x. x^2 ≡ a [MOD p]} = 2*p - 1"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_7: undefined oops


(*
problem_number:5_13
natural language statement:
Show that any prime divisor of $x^{4}-x^{2}+1$ is congruent to 1 modulo 12 .
lean statement:
theorem exercise_5_13 {p x: ℤ} (hp : prime p) 
  (hpx : p ∣ (x^4 - x^2 + 1)) : p ≡ 1 [ZMOD 12] :=

codex statement:
theorem prime_divisor_of_x_4_minus_x_2_plus_1_cong_1_mod_12:
  fixes p::nat
  assumes "prime p" "p dvd (x^4 - x^2 + 1)"
  shows "p ≡ 1 (mod 12)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_13: undefined oops


(*
problem_number:5_27
natural language statement:
Suppose that $f$ is such that $b \equiv a f(p)$. Show that $f^{2} \equiv-1(p)$ and that $2^{(p-1) / 4} \equiv$ $f^{a b / 2}(p)$
lean statement:

codex statement:
theorem square_eq_minus_one_of_equiv_a_f_p:
  fixes f::"int ⇒ int" and a b p::int
  assumes "∀x. f (f x) = -1" "b ≡ a * f p [MOD p]"
  shows "f p ≡ a * b / 2 [MOD p]"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_27: undefined oops


(*
problem_number:5_28
natural language statement:
Show that $x^{4} \equiv 2(p)$ has a solution for $p \equiv 1(4)$ iff $p$ is of the form $A^{2}+64 B^{2}$.
lean statement:
theorem exercise_5_28 {p : ℕ} (hp : p.prime) (hp1 : p ≡ 1 [MOD 4]): 
  ∃ x, x^4 ≡ 2 [MOD p] ↔ ∃ A B, p = A^2 + 64*B^2 :=

codex statement:
theorem exists_solution_of_x_4_eq_2_of_p_1_4:
  fixes p::nat
  assumes "prime p" "p ≡ 1 (mod 4)"
  shows "∃x. x^4 ≡ 2 (mod p)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_28: undefined oops


(*
problem_number:5_37
natural language statement:
Show that if $a$ is negative then $p \equiv q(4 a), p \times a$ implies $(a / p)=(a / q)$.
lean statement:
theorem exercise_5_37 {p q : ℕ} [fact(p.prime)] [fact(q.prime)] {a : ℤ}
  (ha : a < 0) (h0 : p ≡ q [ZMOD 4*a]) (h1 : ¬ ((p : ℤ) ∣ a)) :
  legendre_sym p a = legendre_sym q a :=

codex statement:
theorem eq_of_div_of_eq_div_of_eq_of_mult_eq_zero:
  fixes a p q::int
  assumes "a < 0" "p ≡ q (4 * a)" "p * a = 0"
  shows "a / p = a / q"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_37: undefined oops


(*
problem_number:6_18
natural language statement:
Show that there exist algebraic numbers of arbitrarily high degree.
lean statement:

codex statement:
theorem exists_algebraic_of_degree_succ:
  fixes n::nat
  shows "∃x::'a::algebra_1. algebraic x ∧ degree x = n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_18: undefined oops


(*
problem_number:7_6
natural language statement:
Let $K \supset F$ be finite fields with $[K: F]=3$. Show that if $\alpha \in F$ is not a square in $F$, it is not a square in $K$.
lean statement:

codex statement:
theorem not_square_of_not_square_of_degree_three:
  fixes F::"'a::field" and K::"'b::field"
  assumes "finite_field F" "finite_field K" "F ⊆ K" "[K:F] = 3" "∀x∈F. x^2 ≠ α"
  shows "∀x∈K. x^2 ≠ α"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_6: undefined oops


(*
problem_number:7_24
natural language statement:
Suppose that $f(x) \in \mathbb{Z} / p \mathbb{Z}[x]$ has the property that $f(x+y)=f(x)+$ $f(y) \in \mathbb{Z} / p \mathbb{Z}[x, y]$. Show that $f(x)$ must be of the form $a_{0} x+a_{1} x^{p}+a_{2} x^{p^{2}}+$ $\cdots+a_{m} x^{p^{m}}$.
lean statement:

codex statement:
theorem exists_poly_of_additive_poly:
  fixes p::nat and f::"int poly"
  assumes "∀x y. f (x + y) = f x + f y"
  shows "∃a. f = (∑i<p. a i * X^(p^i))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_24: undefined oops


(*
problem_number:12_12
natural language statement:
Show that $\sin (\pi / 12)$ is an algebraic number.
lean statement:
theorem exercise_12_12 : is_algebraic ℚ (sin (real.pi/12)) :=

codex statement:
theorem algebraic_of_sin_pi_12:
  shows "algebraic (sin (π / 12))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_12_12: undefined oops


(*
problem_number:12_19
natural language statement:
Show that a finite integral domain is a field.
lean statement:

codex statement:
theorem finite_integral_domain_is_field:
  fixes R::"'a::comm_ring_1"
  assumes "finite (carrier R)" "∀x∈carrier R. x ≠ 0 ⟶ ∃y∈carrier R. y * x = 1"
  shows "field R"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_12_19: undefined oops


(*
problem_number:12_22
natural language statement:
Let $F \subset E$ be algebraic number fields. Show that any isomorphism of $F$ into $\mathbb{C}$ extends in exactly $[E: F]$ ways to an isomorphism of $E$ into $\mathbb{C}$.
lean statement:

codex statement:
theorem exists_extension_of_isomorphism_of_algebraic_number_field:
  fixes F E::"'a::{field_char_0, algebraic_semidom}"
  assumes "F ⊆ E" "algebraic_semidom F" "algebraic_semidom E" "isomorphism F ℂ"
  shows "∃f. isomorphism E ℂ ∧ ∀x∈F. f x = (isomorphism_to_complex F) x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_12_22: undefined oops


(*
problem_number:12_30
natural language statement:
Let $p$ be an odd prime and consider $\mathbb{Q}(\sqrt{p})$. If $q \neq p$ is prime show that $\sigma_{q}(\sqrt{p})=$ $(p / q) \sqrt{p}$ where $\sigma_{q}$ is the Frobenius automorphism at a prime ideal in $\mathbb{Q}(\sqrt{p})$ lying above $q$.
lean statement:

codex statement:
theorem frobenius_automorphism_of_prime_ideal_of_sqrt_prime:
  fixes p q::nat
  assumes "prime p" "prime q" "q ≠ p"
  shows "frobenius_automorphism (prime_ideal_of_sqrt_prime p q) = (λx. (p / q) * x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_12_30: undefined oops


(*
problem_number:18_1
natural language statement:
Show that $165 x^{2}-21 y^{2}=19$ has no integral solution.
lean statement:
theorem exercise_18_1 : ¬ ∃ x y : ℤ, 165*x^2 - 21*y^2 = 19 := 

codex statement:
theorem no_integral_solution_of_165_x_square_minus_21_y_square_eq_19:
  assumes "∃x y::int. 165 * x^2 - 21 * y^2 = 19"
  shows False
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_18_1: undefined oops


(*
problem_number:18_4
natural language statement:
Show that 1729 is the smallest positive integer expressible as the sum of two different integral cubes in two ways.
lean statement:
theorem exercise_18_4 {n : ℕ} (hn : ∃ x y z w : ℤ, 
  x^3 + y^3 = n ∧ z^3 + w^3 = n ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w) : 
  n ≥ 1729 :=

codex statement:
theorem smallest_positive_integer_expressible_as_sum_of_two_different_integral_cubes_in_two_ways:
  fixes a b c d::nat
  assumes "a^3 + b^3 = c^3 + d^3" "a^3 ≠ b^3" "c^3 ≠ d^3" "a^3 + b^3 = 1729"
  shows "∀x y z w::nat. x^3 + y^3 = z^3 + w^3 ⟶ x^3 ≠ y^3 ⟶ z^3 ≠ w^3 ⟶ x^3 + y^3 ≥ 1729"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_18_4: undefined oops


(*
problem_number:18_32
natural language statement:
Let $d$ be a square-free integer $d \equiv 1$ or 2 modulo 4 . Show that if $x$ and $y$ are integers such that $y^{2}=x^{3}-d$ then $(x, 2 d)=1$.
lean statement:

codex statement:
theorem gcd_eq_one_of_square_free_cong_one_or_two_mod_four:
  fixes d::int and x y::nat
  assumes "square_free d" "d ≡ 1 ∨ d ≡ 2 [MOD 4]" "y^2 = x^3 - d"
  shows "gcd x (2*d) = 1"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_18_32: undefined oops




end