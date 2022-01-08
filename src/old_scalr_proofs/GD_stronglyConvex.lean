/-
This file contains a formal computer proof of the linear convergence of gradient descent with 
constant stepsize for strongly-convex functions. This file only covers
functions on scalar inputs. The file "GDvec_stronglyConvex.lean" extends this
to vectors. It is self-contained other than using properties of real and 
natural numbers defined in mathlib. I define the properties of strong convexity
and Lipschitz continuous gradient here and do not rely on the 
mathlib-defined gradient. 

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

/- I take the below to be the **definition** of strongly convex + Lipschitz continuous 
   functions. This property can be derived fairly easily. 
-/
def is_strongconvex_LipGrad (gradf : ℝ → ℝ) (m L : ℝ): Prop := 
  ∀ (x y : ℝ),  (gradf(x)-gradf(y))*(x-y) ≥ 
               (m*L/(m+L))*(x-y)^2 + (1/(m+L))*(gradf(x)-gradf(y))^2


-- a one-step contraction lemma 
lemma strongconvex_onestep (η m L : ℝ) (x xstar : ℝ) (gradf : ℝ → ℝ)
                        (hη_low : η ≥ 0) 
                        (hη_up : η ≤ 2/(m+L)) 
                        (h_strongconv_lip : is_strongconvex_LipGrad gradf m L)
                        (hxstar : gradf xstar = 0)
                        :
      (x - η*gradf x - xstar)^2
      ≤ (1-2*η*m*L/(m+L))*(x - xstar)^2
   :=
begin 
  have h0 : x - η * gradf x - xstar = x - xstar - η * gradf x
  := sub_right_comm x (η * gradf x) xstar,
  rw h0,
  have h1 : (x - xstar - η * gradf x) ^ 2 = (x-xstar)^2 - 2*(x-xstar)*η*gradf x + (η*gradf x)^2 
  := by ring,
  rw h1,

  let h2 := h_strongconv_lip x xstar,
  rw hxstar at h2,
  rw sub_zero at h2,

  let h3 := mul_le_mul_of_nonneg_left h2 hη_low,

  have h_2 : (2:ℝ) ≥ 0 := by norm_num,

  let h4 := mul_le_mul_of_nonneg_left h3 h_2,

  have h5 : 2 * (η * (m * L / (m + L) * (x - xstar) ^ 2 + 1 / (m + L) * gradf x ^ 2))
            = 2 * η * m * L / (m + L) * (x - xstar) ^ 2 + 2 * η * 1 / (m + L) * gradf x ^ 2
            := by ring,
  rw h5 at h4,

  have h6: 2 * (η * (gradf x * (x - xstar))) = 2 * (x - xstar) * η * gradf x
        := by ring,
  rw ← h6,
  
  have h7 : 2 * η * m * L / (m + L) * (x - xstar) ^ 2 
            + 2 * η * 1 / (m + L) * gradf x ^ 2 + (x - xstar) ^ 2
            ≤ 2 * (η * (gradf x * (x - xstar))) + (x - xstar) ^ 2
          := by linarith,

  have h8 :  2 * η * 1 / (m + L) * gradf x ^ 2 + (x - xstar) ^ 2
            - 2 * (η * (gradf x * (x - xstar))) 
            ≤ (x - xstar) ^ 2 - 2 * η * m * L / (m + L) * (x - xstar) ^ 2 
          := by linarith,

  have h8_1 : 2 * η * 1 / (m + L) =  η * 2 / (m + L) := by ring,
  rw h8_1 at h8,

  have h8_2 : η*η ≤ η*(2 / (m + L)) := by exact mul_le_mul_of_nonneg_left hη_up hη_low,
  
  have h8_3 : η*(2 / (m + L)) = 2 * η * 1 / (m + L) := by ring,


  rw h8_3 at h8_2,

  have h8_4 : gradf x ^ 2 ≥ 0 := sq_nonneg (gradf x),

  have h8_5 : η*η*gradf x ^ 2 ≤ 2 * η * 1 / (m + L)*gradf x ^ 2 := by exact mul_mono_nonneg h8_4 h8_2,

  have h9 : η*η*gradf x ^ 2 + (x - xstar) ^ 2
            - 2 * (η * (gradf x * (x - xstar))) 
            ≤ (x - xstar) ^ 2 - 2 * η * m * L / (m + L) * (x - xstar) ^ 2 
          := by linarith,

  have h9_1 : (x - xstar) ^ 2 - 2 * η * m * L / (m + L) * (x - xstar) ^ 2 
              = (1 - 2 * η * m * L / (m + L))*(x - xstar) ^ 2
            := by ring,
  rw h9_1 at h9,

  have h9_2 : η * η * gradf x ^ 2 = (η * gradf x) ^ 2 := by ring,

  rw h9_2 at h9,

  linarith,

end 


-- The main theorem
-- note that we do not say that xstar is the minimizer, just that its gradient is zero.
-- Proving that all minimizers have zero gradients would be extra work. 

theorem strongconvex_grad_descent_conv_rate (n : ℕ) (η m L : ℝ) (x0 xstar : ℝ) (gradf : ℝ → ℝ)
                        (hη_low : η ≥ 0) 
                        (hη_up : η ≤ 2/(m+L)) 
                        (hm : m ≥ 0)
                        (hL : L ≥ 0)
                        (hmL : m + L ≠ 0)
                        (h_strongconv_lip : is_strongconvex_LipGrad gradf m L)
                        (hxstar : gradf xstar = 0)
                        :
      ((grad_descent η x0 gradf n) - xstar)^2
      ≤ ((1-2*η*m*L/(m+L))^n)*(x0 - xstar)^2
   :=
begin
induction n with k hk,
have h0 : grad_descent η x0 gradf 0 = x0 := by refl,
rw h0,
rw pow_zero,
rw one_mul,

have h1 : grad_descent η x0 gradf k.succ  = 
          grad_descent η x0 gradf k - η*gradf(grad_descent η x0 gradf k) := by refl,
rw h1,

have h2 := strongconvex_onestep η m L (grad_descent η x0 gradf k) xstar gradf hη_low hη_up h_strongconv_lip hxstar,

rw pow_succ _ k,

have h2_1 : L*η ≤ L*(2 / (m+L)) := mul_le_mul_of_nonneg_left hη_up hL,

have h2_2 : m*(L*η) ≤ m*(L*(2 / (m+L))) := mul_le_mul_of_nonneg_left h2_1 hm,

have h2_3 : (2:ℝ)≥ 0 := by norm_num,

have h2_4 : 2*(m*(L*η)) ≤ 2*(m*(L*(2 / (m+L)))) := mul_le_mul_of_nonneg_left h2_2 h2_3,

have h2_5 : (m+L) ≥ 0 := by linarith,

have h2_6 : 2*(m*(L*η))/(m+L) ≤ 2*(m*(L*(2 / (m+L))))/(m+L) := div_le_div_of_le h2_5 h2_4,

have h2_7 : 2*(m*(L*η))/(m+L) = 2* m* L*η /(m+L) := by ring,

rw h2_7 at h2_6,

have h2_8 : 2*(m*(L*(2 / (m+L))))/(m+L)  = 2*m*L* 2 /(m+L)/(m+L) := by ring,

rw h2_8 at h2_6,

have h2_9 : 2*m*L* 2 /(m+L)/(m+L) = 4*m*L /(m+L)/(m+L) := by ring,

rw h2_9 at h2_6,

have h2_10 : 4*m*L /(m+L)/(m+L) = 4*m*L /((m+L)*(m+L)) := div_div_eq_div_mul (4 * m * L) (m + L) (m + L),

rw h2_10 at h2_6,

have h2_11 : 4*m*L /((m+L)*(m+L)) = 4*m*L /((m+L)^2),
  rw ← pow_two,
rw h2_11 at h2_6,

have h3 : 1 - 2 * m * L * η / (m + L) ≥ 1 -  4 * m * L / (m + L) ^ 2 := by linarith,

have h3_1 : (m + L) ^ 2 ≠ 0 := pow_ne_zero 2 hmL,
have h3_2 : 1 = (m + L) ^ 2 / (m + L) ^ 2 := by exact (div_self h3_1).symm,

have h3_3 : 1 -  4 * m * L / (m + L) ^ 2 = (m + L) ^ 2 / (m + L) ^ 2 -  4 * m * L / (m + L) ^ 2
    := by linarith,

rw h3_3 at h3,


have h3_4 : (m + L) ^ 2 / (m + L) ^ 2 -  4 * m * L / (m + L) ^ 2
          = ((m + L) ^ 2 -  4 * m * L) / (m + L) ^ 2
          := div_sub_div_same ((m + L) ^ 2) (4 * m * L) ((m + L) ^ 2),

rw h3_4 at h3,

have h3_5 : (m + L) ^ 2 -  4 * m * L = m^2 + 2*m*L+L^2 - 4*m*L := by ring,

rw h3_5 at h3,

have h3_6 : m^2 + 2*m*L+L^2 - 4*m*L  = m^2 - 2*m*L + L^2 := by ring,

rw h3_6 at h3,

have h3_7 : m^2 - 2*m*L + L^2 = (m-L)^2 := by ring,

rw h3_7 at h3,

have h3_8 : (m - L) ^ 2 / (m + L) ^ 2 = ((m - L) / (m + L) )^ 2 := by exact (div_pow (m - L) (m + L) 2).symm,

rw h3_8 at h3,

have h3_9 : ((m - L) / (m + L) )^ 2 ≥ 0 := sq_nonneg ((m - L) / (m + L)),

have h4 : 1 - 2 * m * L * η / (m + L) ≥ 0 := by linarith,
have h4_1 : 1 - 2 * m * L * η / (m + L)
          = 1 - 2 * η * m * L / (m + L) := by ring,
rw h4_1 at h4,

have h5 : (1 - 2 * η * m * L / (m + L)) * (grad_descent η x0 gradf k - xstar) ^ 2
    ≤ (1 - 2 * η * m * L / (m + L))*((1 - 2 * η * m * L / (m + L)) ^ k * (x0 - xstar) ^ 2)
    := by exact mul_le_mul_of_nonneg_left hk h4,

have h5_1 : (1 - 2 * η * m * L / (m + L))*((1 - 2 * η * m * L / (m + L)) ^ k * (x0 - xstar) ^ 2)
      = 
      (1 - 2 * η * m * L / (m + L))*(1 - 2 * η * m * L / (m + L)) ^ k * (x0 - xstar) ^ 2
      := by ring,
rw h5_1 at h5,

linarith,

end 
