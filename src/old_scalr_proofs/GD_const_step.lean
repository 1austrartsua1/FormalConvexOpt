/-
This file contains a formal computer proof of O(1/k) convergence of gradient descent with 
constant stepsize for convex functions of scalar-valued inputs. It is self-contained 
other than using properties of real and natural numbers defined in mathlib.  
I define the properties of convexity and Lipschitz continuous gradient here
and do not rely on the mathlib-defined gradient. This means that a user 
would have to ensure that their function is convex and the gradient is correct.
While not ideal, this simplified the proofs. 

We closely follow the proof of
http://www.seas.ucla.edu/~vandenbe/236C/lectures/gradient.pdf
-/

import data.real.basic 

-- The method under study 
-- This is a polymorphic definition in that it works for any Type α that has
-- a subtraction operation and a multiplication operation.
-- This allows us to reason about behavior for the case α = ℝ but also 
-- run it when α = float. We will only prove theorems for α = ℝ. 
def grad_descent {α : Type}
            [has_sub α]
            [has_mul α]
            (η : α) (x0 : α) (gradf : α → α): (ℕ → α) 
| 0      := x0 
| (n+1)  := grad_descent(n) - η*gradf(grad_descent(n))
 
-- Definition of a convex function and it's gradient. 
def is_convex (f: ℝ → ℝ) (gradf : ℝ → ℝ) : Prop := 
  ∀ (x y : ℝ), f(y) ≥  f(x) + gradf(x)*(y-x)

-- (Working) Definition of Lipschitz-continuous gradient
def is_lip_grad (f: ℝ → ℝ) (gradf : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ (x y : ℝ), f(y) ≤ f(x) + gradf(x)*(y-x) + 0.5*L*(y-x)^2 

-- A basic descent lemma for gradient descent 
lemma basic_grad_step (x : ℝ) (η L : ℝ) (f gradf : ℝ → ℝ) 
                      (hlip : is_lip_grad f gradf L)
                      :
  f(x-η*gradf x) ≤ f(x) - η*(1-L*η/2)*(gradf x)^2 
  :=
begin
  have hLip := hlip x (x-η*gradf x),
    
  rw mul_comm η (gradf x) at hLip,
  
  have h1 : x - gradf x * η - x = - gradf x * η := by linarith,
  rw h1 at hLip,
  have h2 : 1 / 2 * L * (-gradf x * η) ^ 2 = 1 / 2 * L * (gradf x)^2 * η^2 
  := by ring,
  rw h2 at hLip,
  have h3 : gradf x * (-gradf x * η) = - η*(gradf x)^2 := by ring,
  rw h3 at hLip,
  have h4 : 1 / 2 * L * gradf x ^ 2 * η ^ 2 = (1 / 2)*(η ^ 2) * L * gradf x^2
  := by ring,
  rw h4 at hLip,
  have h5 :f x + -η * gradf x ^ 2 + 1 / 2 * η ^ 2 * L * gradf x ^ 2 
            = f x -η*(1 -  η * L/2) * gradf x^2
            := by linarith,
  
  rw h5 at hLip,
  rw mul_comm (gradf x) η at hLip,
  rw mul_comm η L at hLip,
  exact hLip,
  
end 

-- an algebraic manipulation lemma 
lemma complete_square (a b t : ℝ) (ht : t > 0): 
  a*b - (t/2)*a^2 = (1/(2*t))*(b^2 - (b-t*a)^2)
  :=
begin
  have h1 : (b-t*a)^2 = b^2 - 2*b*t*a + (t*a)^2,
  {
    rw sub_sq,
    ring,
  },
  rw h1,
  have h2 :b ^ 2 - (b ^ 2 - 2 * b * t * a + (t * a) ^ 2) = 
      2 * b * t * a - (t * a) ^ 2 := by linarith,
  rw h2,
  have h3 : 1 / (2 * t) * (2 * b * t * a - (t * a) ^ 2) = 
            1 / (2 * t) * 2 * b * t * a - 1 / (2 * t)*(t * a) ^ 2
          := by ring,
  rw h3,
  simp,
  have h4 : (2*t)⁻¹ = 2⁻¹*t⁻¹ := mul_inv₀,
  rw h4,
  rw pow_two (t*a),
  have h5 :  2⁻¹ * t⁻¹ * (t * a * (t * a)) = 2⁻¹ * (t⁻¹ * t) * a * (t * a) 
    := by ring,
  rw h5,
  have ht2 : t ≠ 0 := by linarith,
  rw mul_comm t⁻¹ t,

  rw mul_inv_cancel ht2,
  rw mul_one,

  have h6 : 2⁻¹ * t⁻¹ * 2 * b * t * a = 2⁻¹ * 2 * (t⁻¹ * t) * b  * a := by ring,
  rw h6,
  rw mul_comm t⁻¹ t,
  rw mul_inv_cancel ht2,
  rw mul_one,
  have h7 : 2⁻¹ * 2 * b * a = b*a := by ring,
  rw h7,
  
  have h8 : 2⁻¹ * a * (t * a) = 2⁻¹ * t * a * a := by ring,
  rw h8,
  rw div_eq_inv_mul,
  ring,
 
end 

-- a stepsize technicality 
lemma stepsz_upper (t L : ℝ) (hL : L ≥ 0) (h : t≤1/L): t*L ≤ 1 :=
begin 
  
  cases lt_or_ge 0 L,

  exact (le_div_iff h_1).mp h,

  have h2 : L=0 := by linarith,
  rw h2,
  linarith,
  
end 

-- further refinement of the descent properties of the algorithm 
lemma basic_grad_step_v2 (x : ℝ) (η L : ℝ) (f gradf : ℝ → ℝ) 
                      (hL : L ≥ 0)
                      (hη_low : η ≥ 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      :
    f(x-η*gradf x) ≤ f(x) -(η/2)*(gradf x)^2 
  :=
  begin
    have hbas := basic_grad_step x η L f gradf hlip,
    have hgradPos : gradf x ^2 ≥ 0 := by exact sq_nonneg (gradf x),

    have hCoefPos : η*(1-L*η/2) ≥ η/2,
    {

      have h3 : η*L ≤ 1 := by exact stepsz_upper η L hL hη2,

      have h4 : L*η≤ 1 := by linarith,
      have h5 : L*η/2 ≤ 1/2 := by linarith,
      have h6 : -L*η/2 ≥  -1/2 := by linarith,
      have h7 : 1-L*η/2 ≥  1/2 := by linarith,
      have h8 : η*(1-L*η/2) ≥  η*(1/2) 
              := by exact mul_le_mul_of_nonneg_left h7 hη_low,
      linarith,
    },
    
    have h9 : η*(1-L*η/2)*(gradf x)^2 ≥ (η/2)*(gradf x)^2 :=
      mul_mono_nonneg hgradPos hCoefPos,
    
    linarith,
    
  end 

-- formally stating that the algorithm decreases function values 
lemma descent (x : ℝ) (η L : ℝ) (f gradf : ℝ → ℝ) 
                      (hL : L ≥ 0)
                      (hη_low : η ≥ 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      :
    f(x-η*gradf x) ≤ f(x) 
  :=
begin
  have hbas := basic_grad_step_v2 x η L f gradf hL hη_low hη2 hlip,
  have hgradPos : gradf x ^2 ≥ 0 := by exact sq_nonneg (gradf x),
  have h2 : η / 2 ≥ 0 := by linarith,
  have h3 : (η / 2)*(gradf x)^2 ≥ 0 := mul_nonneg h2 hgradPos,
  linarith,
end 

lemma prepare_to_telescope (x y: ℝ) (η L : ℝ) (f gradf : ℝ → ℝ) 
                      (hL : L ≥ 0)
                      (hη_low : η > 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      (hconv : is_convex f gradf)
                      :
    f(x-η*gradf x) - f y ≤ (1/(2*η))*((x-y)^2 - (x-η*gradf x - y)^2)
    :=
begin 
  
  have hη_low2 : η ≥ 0 := by linarith,

  have h1 := basic_grad_step_v2  x η L f gradf hL hη_low2 hη2 hlip,
  
  have h2 :  f (x - η * gradf x) -f y ≤ f x - f y - η / 2 * gradf x ^ 2 
    := by linarith,

  have h3 := hconv x y,

  have h4 :  f x - f y ≤ - gradf x * (y - x) := by linarith,
  have h5 : - gradf x * (y - x) = gradf x * (x - y) := by linarith,
  rw h5 at h4,
  have h6 : f (x - η * gradf x) - f y ≤ 
    gradf x * (x - y)- η / 2 * gradf x ^ 2 := by linarith,

  have h7 : gradf x * (x - y) - η / 2 * gradf x ^ 2
    = (1/(2*η))*((x-y)^2 - (x-y - η*gradf x)^2)
    := by exact complete_square  (gradf x) (x-y) (η) (hη_low), 
  
  rw h7 at h6,
  linarith,
    
end 

-- rewrite the telescoping more favorably 
lemma prepare_to_telescope2 (x0 y: ℝ) (n : ℕ) (η L : ℝ) (f gradf : ℝ → ℝ) 
                      (hL : L ≥ 0)
                      (hη_low : η > 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      (hconv : is_convex f gradf)
                      :
    f(grad_descent η x0 gradf (n+1)) - f y ≤ 
    (1/(2*η))*((grad_descent η x0 gradf n-y)^2 - (grad_descent η x0 gradf (n+1) - y)^2)
    :=
begin 

  have h1 : grad_descent η x0 gradf (n+1) = 
            grad_descent η x0 gradf (n) - η*gradf(grad_descent η x0 gradf (n))
          := by refl,
  rw h1,

  exact prepare_to_telescope (grad_descent η x0 gradf (n)) y η L f gradf hL hη_low hη2 hlip hconv,

end 

-- sum_f is just the sum of function values evaluated at the points 
-- generated by the algorithm (again defined recursively)
def sum_f (y x0 : ℝ) (f : ℝ → ℝ) (η : ℝ) (gradf : ℝ → ℝ): (ℕ → ℝ)
| 0      := 0
| (n+1)  := sum_f(n) + f(grad_descent η x0 gradf (n+1)) - f y


-- the all important telescoping result 
lemma telescope (x0 y: ℝ) (n : ℕ) (η L : ℝ) (f gradf : ℝ → ℝ) 
                      (hL : L ≥ 0)
                      (hη_low : η > 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      (hconv : is_convex f gradf)
                      :
    sum_f y x0 f η gradf (n) ≤ (1/(2*η))*((x0-y)^2 - (grad_descent η x0 gradf n  - y)^2)
    :=
begin 
  induction n with k hk,

  have h1 : grad_descent η x0 gradf 0 = x0 := by refl,
  rw h1,

  have h2 : 1 / (2 * η) * ((x0 - y) ^ 2 - (x0 - y) ^ 2) = 0 := by linarith,
  rw h2,
  refl,
  
  have h3 : sum_f y x0 f η gradf k.succ = sum_f y x0 f η gradf k +
       f(grad_descent η x0 gradf (k+1)) - f y := by refl,
  rw h3,
  
  have h4 := prepare_to_telescope2 x0 y k η L f gradf hL hη_low hη2 hlip hconv, 

  linarith,
  
end 

-- a simple upper bound derived from telescoping 
lemma from_telescope (x0 y: ℝ) (n : ℕ) (η L : ℝ) (f gradf : ℝ → ℝ) 
                      (hL : L ≥ 0)
                      (hη_low : η > 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      (hconv : is_convex f gradf)
                      :
    sum_f y x0 f η gradf (n) ≤ (1/(2*η))*(x0-y)^2 
    :=
begin 
  have h := telescope x0 y n η L f gradf hL hη_low hη2 hlip hconv,

  have h1 : (grad_descent η x0 gradf n - y) ^ 2 ≥ 0 
    := sq_nonneg (grad_descent η x0 gradf n - y),
  
  have h2 : 1 / (2 * η) * ((x0 - y) ^ 2 - (grad_descent η x0 gradf n - y) ^ 2)
          =  1 / (2 * η)*(x0 - y) ^ 2 - 1 / (2 * η) *(grad_descent η x0 gradf n - y) ^ 2
    := mul_sub (1 / (2 * η)) ((x0 - y) ^ 2) ((grad_descent η x0 gradf n - y) ^ 2),
  
  rw h2 at h,

  have h3 : 1 / (2 * η) ≥ 0,
  {
    have h4 : 2 * η ≥ 0 := by linarith,
    exact one_div_nonneg.mpr h4,
  },
  have h5 : 1 / (2 * η) * (grad_descent η x0 gradf n - y) ^ 2 ≥ 0
    := mul_nonneg h3 h1,
  linarith,
end 

-- since func values are decreasing, the sum of func vals provides 
-- a bound on the last function value as follows
lemma last_less_than_av (x0 y: ℝ) (n : ℕ) (η L : ℝ) (f gradf : ℝ → ℝ) 
                      (hL : L ≥ 0)
                      (hη_low : η > 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      (hconv : is_convex f gradf)
                      :
    sum_f y x0 f η gradf (n) ≥ n*(f(grad_descent η x0 gradf n) - f y)
    :=
begin 
  induction n with k hk,
  have h : ↑0 = (0:ℝ):= nat.cast_zero,
  rw h,
  rw zero_mul,
  have h1 : sum_f y x0 f η gradf 0 = 0 := by refl,
  rw h1,
  exact rfl.ge,

  have h2 : sum_f y x0 f η gradf k.succ = sum_f y x0 f η gradf (k) + f(grad_descent η x0 gradf (k+1)) - f y
    := by refl,

  rw h2,


  rw nat.succ_eq_add_one,
  have h3 : ↑(k+1) = (k+1 : ℝ):= nat.cast_succ k,
  rw h3,
  have h4 : (↑k + 1) * (f (grad_descent η x0 gradf (k + 1)) - f y)
            = ↑k*(f (grad_descent η x0 gradf (k + 1)) - f y) 
              + f (grad_descent η x0 gradf (k + 1)) - f y
          := by linarith,
  rw h4,


  have hη_low2 : η ≥ 0 := by linarith,

  have hdesc := descent (grad_descent η x0 gradf k) η L f gradf hL hη_low2 hη2 hlip, 

  have h5 : grad_descent η x0 gradf (k+1) = 
        grad_descent η x0 gradf k - η * gradf (grad_descent η x0 gradf k)
    := by refl,
  
  rw ← h5 at hdesc,

  
  have h6 : ↑k * f (grad_descent η x0 gradf (k + 1)) ≤ ↑k * f (grad_descent η x0 gradf k),
  {
    have hupk : (0:ℝ) ≤ (↑k)  := nat.cast_nonneg k,

    exact mul_le_mul_of_nonneg_left hdesc hupk,

  },

  linarith,

end 

-- Main convergence rate result 
-- Note that y is an arbitrary point but it is customarily taken to 
-- be one of the minimizers (assuming minimizers exist)
theorem grad_descent_convergence_rate (n : ℕ) (η L : ℝ) (x0 y : ℝ) (f gradf : ℝ → ℝ)
                        (hn : n ≥ 1)
                        (hη_low : η > 0) 
                        (hη_up : η ≤ 1/L) 
                        (hL : L ≥ 0)
                        (hconv : is_convex f gradf)
                        (hlip : is_lip_grad f gradf L)
                        :
      f(grad_descent η x0 gradf n) - f(y)≤ (1/(2*η*n))*(x0-y)^2
   :=
begin
  
  have h0 := from_telescope x0 y n η L f gradf hL hη_low hη_up hlip hconv,
  
  have h1 := last_less_than_av x0 y n η L f gradf hL hη_low hη_up hlip hconv,

  have h2 : ↑n * (f (grad_descent η x0 gradf n) - f y) ≤ 1 / (2 * η) * (x0 - y) ^ 2
   := by linarith,

  have h3 :  (f (grad_descent η x0 gradf n) - f y) ≤ 1 / (2 * η) * (x0 - y) ^ 2 / ↑n,
  {
    have h4 : ↑n≥ (1:ℝ) := nat.one_le_cast.mpr hn,
    
    have h5 : ↑n > (0:ℝ) := by linarith,

    exact (le_div_iff' h5).mpr h2,
  },
   
  have h6 : 1 / (2 * η) * (x0 - y) ^ 2 / ↑n = (1/↑n)*1 / (2 * η) * (x0 - y) ^ 2
    := by ring,
  
  have h7 : (1/↑n)*1 / (2 * η) 
            = 1 / (2 * η * ↑n),
  {
    ring,
    exact mul_inv₀.symm,
  },
  rw h6 at h3,
  rw h7 at h3,
  exact h3,

end   
  
  



