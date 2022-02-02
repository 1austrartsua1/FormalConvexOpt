/-
This file contains a formal computer proof of O(1/k) convergence of gradient descent with 
constant stepsize for convex functions on a real inner-product space. It is self-contained other than using properties of real and natural numbers defined in mathlib.  
I define the properties of convexity and Lipschitz continuous gradient here
and do not rely on the mathlib-defined gradient. This means that a user 
would have to ensure that their function is convex and the gradient is correct.
While not ideal, this simplified the proofs. 
We closely follow the proof of
http://www.seas.ucla.edu/~vandenbe/236C/lectures/gradient.pdf
-/

import data.real.basic 
import analysis.inner_product_space.pi_L2

-- H is an inner product space over the reals
-- It is an abstract type but [inner_product_space ℝ H] 
-- ensures it satisfies all the properties of a real inner product space.
-- It is interesting to note that we do not need H
-- to be a Hilbert space. This is because, for 
-- nonasymptotic analyses, we do not need the space
-- to be complete as we do not take limits anywhere. 
variables {H : Type*} [inner_product_space ℝ H] 

-- inner product notation, i.e. scalar product. 
notation `⟪`x`, `y`⟫` := @inner ℝ _ _ x y

-- method under study. Note that • means "scalar multiply"
-- i.e. a scalar times a vector. 
-- it is written "backslash+smul"
noncomputable def grad_descent 
            (η : ℝ) (x0 : H) (gradf : H → H): (ℕ → H) 
| 0      := x0 
| (n+1)  := grad_descent(n) - η•gradf(grad_descent(n))

-- Definition of a convex function and it's gradient. 
def is_convex (f: H → ℝ) (gradf : H → H) : Prop := 
  ∀ (x y : H), f(y) ≥  f(x) + ⟪gradf(x),y-x⟫

-- Definition of Lipschitz-continuous gradient
def is_lip_grad (f: H → ℝ) (gradf : H → H) (L : ℝ) : Prop :=
  ∀ (x y : H), f(y) ≤ f(x) + ⟪gradf(x),y-x⟫ + 0.5*L*∥y-x∥^2 

-- some simple helper lemmas 
lemma helper_norm_sq_eq_inner (x : H)
        : ∥x∥^2= ⟪x,x⟫_ℝ
        :=
begin 
  let h := norm_sq_eq_inner x,
  assumption,
end 

lemma helper_inner_neg (x y:H) 
        : ⟪x,-y⟫ = -⟪x,y⟫
        :=
begin 
  exact inner_neg_right,
end 


-- A basic descent lemma for gradient descent 
lemma basic_grad_step (x : H) (η L : ℝ) (f : H → ℝ) (gradf : H → H) 
                      (hlip : is_lip_grad f gradf L)
                      :
  f(x-η•gradf x) ≤ f(x) - η*(1-L*η/2)*∥gradf x∥^2 
  :=
begin
  have HLip := hlip x (x-η•gradf x),

  have h : x - η • gradf x - x = x - x - η • gradf x := by abel,
  rw h at HLip, clear h,
  rw sub_self at HLip,
  rw zero_sub at HLip,
  

  rw inner_neg_right at HLip,
  rw real_inner_smul_right at HLip,
  
  have h1 := helper_norm_sq_eq_inner (gradf x),
  rw ← h1 at HLip,

  rw norm_neg at HLip,
  

  have h : ∥η • gradf x∥ = |η|*∥gradf x ∥  :=  norm_smul η (gradf x),
  rw h at HLip, clear h,
  
  rw mul_pow at HLip,

  have h : |η| ^ 2 = η^2 := sq_abs η,
  rw h at HLip, clear h,

  rw mul_sub,
  rw mul_one,
  rw sub_mul,
  rw ← sub_add,

  have h : 1 / 2 * L * (η ^ 2 * ∥gradf x∥ ^ 2)
          = η * (L * η / 2) * ∥gradf x∥ ^ 2 := by ring,
  rw h at HLip, clear h,
  exact HLip,
  
end 

-- an algebraic manipulation lemma 
lemma complete_square (x y : H) (t : ℝ) (ht : t > 0): 
  ⟪x,y⟫ - (t/2)*∥y∥^2 = (1/(2*t))*(∥x∥^2 - ∥x-t•y∥^2)
  :=
begin 
  rw norm_sub_sq_real,
  have h0 : ∥x∥ ^ 2 - (∥x∥ ^ 2 - 2 * inner x (t • y) + ∥t • y∥ ^ 2)
          = ∥x∥ ^ 2 - ∥x∥ ^ 2 + 2 * inner x (t • y) - ∥t • y∥ ^ 2
          := by abel,
  simp at h0,
  rw h0,
  rw inner_smul_right,
  rw norm_smul,
  have h1 : ∥t∥ = |t| := real.norm_eq_abs t,
  rw h1,
  have h2 : |t| = t := abs_of_pos ht,
  rw h2,
  rw mul_sub,
  have h3 : 1 / (2 * t) * (2 * (t * inner x y)) = 
            (1 / (2 * t)) * 2 * t * inner x y
            := by ring,
  rw h3,
  have h4 : 1 / (2 * t) * 2 * t =  2 / (2 * t) * t
        := by ring,
  rw h4,
  have h5 : 2 / (2 * t) * t = (2*t) / (2 * t) 
        := by ring,
  rw h5,

  have h6 : (2:ℝ)≠ 0:=by norm_num,
  have h7 : t ≠ 0 := ne_of_gt ht,
  have h8 : 2*t ≠ 0 := mul_ne_zero h6 h7,

  have h8 : (2*t) / (2 * t) = 1 := div_self h8,

  rw h8,
  rw one_mul,

  have h9 : (t * ∥y∥) ^ 2  = t^ 2 * ∥y∥ ^ 2
          := mul_pow t (∥y∥) 2,
  rw h9,

  have h10 : 1 / (2 * t) * (t ^ 2 * ∥y∥ ^ 2)
          = t ^ 2 / (2 * t) * ∥y∥ ^ 2
          := by ring,
  
  rw h10,

  rw mul_comm 2 t,

  have h11 : t^2 / (t * 2) = (t ^ 2 / t) / 2 
    := (div_div_eq_div_mul (t^2) t 2).symm,
  rw h11,
  
  rw sq t,
  have h12 : t * t / t = t*(t/t):=by ring,
  rw h12,
  rw div_self h7,
  rw mul_one,

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
lemma basic_grad_step_v2 (x : H) (η L : ℝ) (f : H → ℝ) (gradf : H → H)
                    (hL : L ≥ 0)
                    (hη_low : η ≥ 0) 
                    (hη2 : η ≤ 1/L) 
                    (hlip : is_lip_grad f gradf L)
                    :
  f(x-η•gradf x) ≤ f(x) -(η/2)*∥gradf x∥^2 
:=
begin
  have h := basic_grad_step x η L f gradf hlip,
  rw mul_sub at h,
  rw mul_one at h,
  rw sub_mul at h,
  rw ← sub_add at h,

  have h1 := stepsz_upper η L hL hη2,
  rw mul_comm L _ at h,

  have h2 :  2 > 0 := by norm_num,
  have h3 : η * L /2 ≤ 1 /2 := by nlinarith,
  have h4 : η*(η * L /2)≤ η*1/2 := by nlinarith,
  clear h3,
  
  have h4 : 0 ≤ ∥gradf x∥ ^ 2  := by exact sq_nonneg (∥gradf x∥),
  have h5 : ∥gradf x∥ ^ 2 ≥ 0 := by linarith, clear h4,

  have h6 : η*(η * L /2)*∥gradf x∥ ^ 2 ≤ (η*1/2)*∥gradf x∥ ^ 2
          := by nlinarith,

  clear h4, clear h5,

  have h7 : f (x - η • gradf x) 
            ≤ f x - η * ∥gradf x∥ ^ 2 + (η*1/2)*∥gradf x∥ ^ 2
          := by linarith,
  clear h, clear h6,
  
  rw mul_one at h7,

  rw sub_add at h7,

  rw ← sub_mul at h7,

  have h : η - η / 2 = η/2 := by linarith,
  rw h at h7,
  exact h7,
end 

-- formally stating that the algorithm decreases function values 
lemma descent (x : H) (η L : ℝ) (f : H → ℝ) (gradf : H → H)
                      (hL : L ≥ 0)
                      (hη_low : η ≥ 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      :
    f(x-η•gradf x) ≤ f(x) 
  :=
begin
  have h := basic_grad_step_v2 x η L f gradf hL hη_low hη2 hlip,

  have h2 : 2>0:=by norm_num,
  have h3 : η/2≥0:= by nlinarith,
  have h4 : 0 ≤ ∥gradf x∥ ^ 2  := by exact sq_nonneg (∥gradf x∥),
  have h5 : ∥gradf x∥ ^ 2 ≥ 0 := by linarith, clear h4,

  have h6 : η / 2 * ∥gradf x∥ ^ 2 ≥ 0 := by nlinarith,
  
  linarith,
end 

lemma prepare_to_telescope (x y: H) (η L : ℝ) (f : H → ℝ) (gradf : H → H)
                      (hL : L ≥ 0)
                      (hη_low : η > 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      (hconv : is_convex f gradf)
                      :
    f(x-η•gradf x) - f y ≤ (1/(2*η))*(∥x-y∥^2 - ∥x-η•gradf x - y∥^2)
    :=
begin 
  have hη_low2 : η ≥ 0 := by linarith,
  have h1 := basic_grad_step_v2  x η L f gradf hL hη_low2 hη2 hlip,

  have h2 :  f (x - η • gradf x) -f y ≤ f x - f y - η / 2 * ∥gradf x ∥^ 2 
    := by linarith,
  
  have h3 := hconv x y,

  have h4 : f x-f y ≤  - inner (gradf x) (y - x) := by linarith,

  have h5 := helper_inner_neg (gradf x) (y - x),
  clear h3,
  rw ← h5 at h4, clear h5, 
  have h5 : -(y-x)=x-y:=by abel,
  rw h5 at h4, clear h5,

  have h5 : f(x - η • gradf x) - f y ≤ ⟪gradf x,x-y⟫ - η / 2 * ∥gradf x∥ ^ 2
    := by linarith,
  clear h2,clear h4,clear h1,

  rw real_inner_comm at h5,
  
  have h2 := complete_square (x-y) (gradf x)  η hη_low,
  rw h2 at h5,
  
  have h4 : x - y - η • gradf x = x - η • gradf x - y := sub_right_comm x y (η • gradf x),

  rw h4 at h5,
  exact h5,

end 

-- rewrite the telescoping more favorably 
lemma prepare_to_telescope2 (x0 y: H) (n : ℕ) (η L : ℝ) (f : H → ℝ) (gradf : H → H)
                      (hL : L ≥ 0)
                      (hη_low : η > 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      (hconv : is_convex f gradf)
                      :
    f(grad_descent η x0 gradf (n+1)) - f y ≤ 
    (1/(2*η))*(∥grad_descent η x0 gradf n-y∥^2 - ∥grad_descent η x0 gradf (n+1) - y∥^2)
    :=
begin 
  have h1 : grad_descent η x0 gradf (n+1) = 
            grad_descent η x0 gradf (n) - η•gradf(grad_descent η x0 gradf (n))
          := by simp [grad_descent],
  
  rw h1,
  clear h1,
  exact prepare_to_telescope (grad_descent η x0 gradf (n)) y η L f gradf hL hη_low hη2 hlip hconv,

end 

-- sum_f is just the sum of function values evaluated at the points 
-- generated by the algorithm (again defined recursively)
noncomputable def sum_f (y x0 : H) (f : H → ℝ) (η : ℝ) (gradf : H → H): (ℕ → ℝ)
| 0      := 0
| (n+1)  := sum_f(n) + f(grad_descent η x0 gradf (n+1)) - f y

-- the all important telescoping result 
lemma telescope (x0 y: H) (n : ℕ) (η L : ℝ) (f : H → ℝ) (gradf : H → H) 
                      (hL : L ≥ 0)
                      (hη_low : η > 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      (hconv : is_convex f gradf)
                      :
    sum_f y x0 f η gradf (n) ≤ (1/(2*η))*(∥x0-y∥^2 - ∥grad_descent η x0 gradf n  - y∥^2)
    :=
begin 
  induction n with k hk,
  have h1 : grad_descent η x0 gradf 0 = x0 := by refl,
  rw h1,
  
  have h2 : 1 / (2 * η) * (∥x0 - y∥ ^ 2 - ∥x0 - y∥ ^ 2) = 0 := by linarith,
  rw h2,
  refl,

  have h : sum_f y x0 f η gradf k.succ = sum_f y x0 f η gradf k +
       f(grad_descent η x0 gradf (k+1)) - f y := by simp [sum_f],
  rw h, clear h,

  have h := prepare_to_telescope2 x0 y k η L f gradf hL hη_low hη2 hlip hconv, 
  linarith,

end 

-- a simple upper bound derived from telescoping 
lemma from_telescope (x0 y: H) (n : ℕ) (η L : ℝ) (f : H → ℝ) (gradf : H → H)
                      (hL : L ≥ 0)
                      (hη_low : η > 0) 
                      (hη2 : η ≤ 1/L) 
                      (hlip : is_lip_grad f gradf L)
                      (hconv : is_convex f gradf)
                      :
    sum_f y x0 f η gradf (n) ≤ (1/(2*η))*∥x0-y∥^2 
    :=
begin 
  have h := telescope x0 y n η L f gradf hL hη_low hη2 hlip hconv,

  have h1 : ∥grad_descent η x0 gradf n - y∥ ^ 2 ≥ 0 
    := sq_nonneg (∥grad_descent η x0 gradf n - y∥),
  
  rw mul_sub at h,
  have h2 : 2 > 0 := by norm_num,
  have h3 : 2*η > 0 := by nlinarith,
  have h5 : 1 / (2*η) >0 := one_div_pos.mpr h3,

  have h6 :  1 / (2 * η) * ∥grad_descent η x0 gradf n - y∥ ^ 2 ≥ 0 
    := by nlinarith,
  linarith,

end 

-- since func values are decreasing, the sum of func vals provides 
-- a bound on the last function value as follows
lemma last_less_than_av (x0 y: H) (n : ℕ) (η L : ℝ) (f : H → ℝ) (gradf : H → H)
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
    := by simp [sum_f],


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
        grad_descent η x0 gradf k - η • gradf (grad_descent η x0 gradf k)
    := by simp [grad_descent],
  

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
theorem grad_descent_convergence_rate (n : ℕ) (η L : ℝ) (x0 y : H) (f : H → ℝ) (gradf : H → H)
                        (hn : n ≥ 1)
                        (hη_low : η > 0) 
                        (hη_up : η ≤ 1/L) 
                        (hL : L ≥ 0)
                        (hconv : is_convex f gradf)
                        (hlip : is_lip_grad f gradf L)
                        :
      f(grad_descent η x0 gradf n) - f(y)≤ (1/(2*η*n))*∥x0-y∥^2
   :=
begin
  have h0 := from_telescope x0 y n η L f gradf hL hη_low hη_up hlip hconv,
  have h1 := last_less_than_av x0 y n η L f gradf hL hη_low hη_up hlip hconv,

  have h2 : ↑n * (f (grad_descent η x0 gradf n) - f y) ≤ 1 / (2 * η) * ∥x0 - y∥ ^ 2
   := by linarith,
  
  have h3 :  (f (grad_descent η x0 gradf n) - f y) ≤ 1 / (2 * η) * ∥x0 - y∥ ^ 2 / ↑n,
  {
    have h4 : ↑n≥ (1:ℝ) := nat.one_le_cast.mpr hn,
    
    have h5 : ↑n > (0:ℝ) := by linarith,

    exact (le_div_iff' h5).mpr h2,
  },
  clear h2,

  have h6 : 1 / (2 * η) * ∥x0 - y∥ ^ 2 / ↑n = (1/↑n)*1 / (2 * η) * ∥x0 - y∥ ^ 2
    := by ring,
  
  have h7 : (1/↑n)*1 / (2 * η) 
            = 1 / (2 * η * ↑n),
  {
    ring_nf,
    exact mul_inv₀.symm,
  },
  rw h6 at h3,
  rw h7 at h3,
  exact h3,

end 
