/-
This file contains a formal computer proof of the linear convergence of gradient descent with 
constant stepsize for strongly-convex functions defined on a real inner product. 
It is self-contained , other than using properties of real, natural numbers, and real inner 
product spaces defined in mathlib. I define the properties of strong convexity and 
Lipschitz continuous gradient here and do not rely on the mathlib-defined gradient. 

We closely follow the proof of
http://www.seas.ucla.edu/~vandenbe/236C/lectures/gradient.pdf
-/

import data.real.basic 
import analysis.inner_product_space.pi_L2

-- H is an inner product space over the reals
-- It is an abstract type but [inner_product_space ℝ H] 
-- ensures it satisfies all the properties of a real inner product space.
-- It is interesting to note that we do not need V
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



/- I take the below to be the **definition** of strongly convex + Lipschitz continuous 
   functions. This property can be derived fairly easily. 
-/
def is_strongconvex_LipGrad (gradf : H → H) (m L : ℝ): Prop := 
  ∀ (x y : H),  ⟪gradf(x)-gradf(y),x-y⟫ ≥ 
               (m*L/(m+L))*∥x-y∥^2 + (1/(m+L))*∥gradf(x)-gradf(y)∥^2


-- a one-step contraction lemma 
lemma strongconvex_onestep (η m L : ℝ) (x xstar : H) (gradf : H → H)
                        (hη_low : η ≥ 0) 
                        (hη_up : η ≤ 2/(m+L)) 
                        (h_strongconv_lip : is_strongconvex_LipGrad gradf m L)
                        (hxstar : gradf xstar = 0)
                        :
      ∥x - η•gradf x - xstar∥^2
      ≤ (1-2*η*m*L/(m+L))*∥x - xstar∥^2
   :=
begin 
  have h : x - η • gradf x - xstar = x - xstar  - η • gradf x  
      := by abel,
  rw h,clear h,

  rw norm_sub_sq_real,

  have h : inner (x - xstar) (η • gradf x) = η*inner (x - xstar) (gradf x) 
    := inner_smul_real_right,
  rw h, clear h,
  

  let h := h_strongconv_lip x xstar,
  rw hxstar at h,
  rw sub_zero at h,

  have h2 : (2:ℝ)≥0 := by norm_num,
  have h0 : 2*η ≥ 0 := mul_nonneg h2 hη_low,

  have h1 : (2*η)*(inner (gradf x) (x - xstar)) 
            ≥ (2*η)*(m * L / (m + L) * ∥x - xstar∥ ^ 2
                    + 1 / (m + L) * ∥gradf x∥ ^ 2)
          := mul_le_mul_of_nonneg_left h h0,
  clear h,

  have h1_0 : (2*η)*(m * L / (m + L) * ∥x - xstar∥ ^ 2
                    + 1 / (m + L) * ∥gradf x∥ ^ 2)
              = (2*η)*m * L / (m + L) * ∥x - xstar∥ ^ 2
                    + (2*η)*1 / (m + L) * ∥gradf x∥ ^ 2
            := by ring,
  rw h1_0 at h1,
  clear h1_0,


  have h :  0 ≥ -2 * η * inner (gradf x) (x - xstar) 
            +2 * η * m * L / (m + L) * ∥x - xstar∥ ^ 2 
            + 2 * η * 1 / (m + L) * ∥gradf x∥ ^ 2
         := by linarith,

  clear h1,

  have h1 :  ∥x - xstar∥ ^ 2  ≥ -2 * η * inner (gradf x) (x - xstar) 
            +2 * η * m * L / (m + L) * ∥x - xstar∥ ^ 2 
            + 2 * η * 1 / (m + L) * ∥gradf x∥ ^ 2
            + ∥x - xstar∥ ^ 2 
         := by linarith,

  clear h,
  have h :  ∥x - xstar∥ ^ 2  - 2 * η * m * L / (m + L) * ∥x - xstar∥ ^ 2 
            ≥ -2 * η * inner (gradf x) (x - xstar)           
            + 2 * η * 1 / (m + L) * ∥gradf x∥ ^ 2
            + ∥x - xstar∥ ^ 2 
         := by linarith,
  clear h1,

  have h1 : -2 * η * inner (gradf x) (x - xstar)           
            + 2 * η * 1 / (m + L) * ∥gradf x∥ ^ 2
            + ∥x - xstar∥ ^ 2  
            ≤ 
            ∥x - xstar∥ ^ 2  - 2 * η * m * L / (m + L) * ∥x - xstar∥ ^ 2 
         := by linarith,
  clear h,

   rw sub_mul,
   rw one_mul,

   have h : 2 * η * 1 / (m + L) = η * 2 / (m + L)
      := by ring,
   rw h at h1, clear h,

   have h : η*η ≤ η * (2 / (m + L)) := mul_le_mul_of_nonneg_left hη_up hη_low,

   have hgrad : ∥gradf x∥ ^ 2 ≥ 0 := sq_nonneg (∥gradf x∥),
   have h_2 : η*η*∥gradf x∥ ^ 2 ≤ η * (2 / (m + L))*∥gradf x∥ ^ 2 
      := mul_mono_nonneg hgrad h,
   have h' :  η * (2 / (m + L)) = η * 2 / (m + L) := by ring,
   rw h' at h_2, 
   
   clear h, clear hgrad, clear h',

   have h : (-2) * η * inner (gradf x) (x - xstar) 
            + η * η * ∥gradf x∥ ^ 2 
            + ∥x - xstar∥ ^ 2 
            ≤ ∥x - xstar∥ ^ 2 - 2 * η * m * L / (m + L) * ∥x - xstar∥ ^ 2
         := by linarith,
   clear h_2, clear h1,

   rw ← sq η at h,
   rw ← mul_pow η _ at h,
   have h1 :|η|= η := abs_of_nonneg hη_low,
   have h_2 : (η * ∥gradf x∥) ^ 2 = (|η| * ∥gradf x∥) ^ 2,
   {
      rw h1,
   },
   clear h1,
   have h1 : ∥η•gradf x∥ = |η| * ∥gradf x∥,
   {exact norm_smul η (gradf x),},
   rw ← h1 at h_2,
   rw h_2 at h,
   clear h1, clear h_2,

   have h1 : (-2) * η * inner (gradf x) (x - xstar)
            =
            - 2 * (η * inner (gradf x) (x - xstar))
         := by ring,

   rw h1 at h,
   clear h1,
   rw real_inner_comm at h,
   linarith,
   
end 


theorem strongconvex_grad_descent_conv_rate (n : ℕ) (η m L : ℝ) (x0 xstar : H) 
                        (gradf : H → H)
                        (hη_low : η ≥ 0) 
                        (hη_up : η ≤ 2/(m+L)) 
                        (hm : m ≥ 0)
                        (hL : L ≥ 0)
                        (hmL : m + L ≠ 0)
                        (h_strongconv_lip : is_strongconvex_LipGrad gradf m L)
                        (hxstar : gradf xstar = 0)
                        :
      ∥(grad_descent η x0 gradf n) - xstar∥^2
      ≤ ((1-2*η*m*L/(m+L))^n)*∥x0 - xstar∥^2
   :=
begin
   induction n with k hk,
   have h0 : grad_descent η x0 gradf 0 = x0 := by refl,
   rw h0,
   rw pow_zero,
   rw one_mul,

   have h1 : grad_descent η x0 gradf (k+1) 
            = grad_descent η x0 gradf k - η•gradf(grad_descent η x0 gradf k),
   {
      simp [grad_descent],
   },
   rw h1,clear h1,
   have h := strongconvex_onestep η m L 
                                 (grad_descent η x0 gradf k) 
                                 xstar gradf hη_low hη_up h_strongconv_lip hxstar,
   rw pow_succ _ k,

   have h1 : L*η ≤ L*(2 / (m+L)) := mul_le_mul_of_nonneg_left hη_up hL,
   have h2 : m*(L*η) ≤ m*(L*(2 / (m+L))) := mul_le_mul_of_nonneg_left h1 hm,
   clear h1,
   have h1 : (2:ℝ)≥ 0 := by norm_num,
   have h3 : 2*(m*(L*η)) ≤ 2*(m*(L*(2 / (m+L)))) := mul_le_mul_of_nonneg_left h2 h1,
   clear h1, clear h2,
   have h1 : (m+L) ≥ 0 := by linarith,

   have h2 : 2*(m*(L*η))/(m+L) ≤ 2*(m*(L*(2 / (m+L))))/(m+L) := div_le_div_of_le h1 h3,
   clear h3, clear h1,
   have h3 : 2*(m*(L*η))/(m+L) = 2* m* L*η /(m+L) := by ring,
   rw h3 at h2, clear h3,
   have h3 : 2*(m*(L*(2 / (m+L))))/(m+L)  = 2*m*L* 2 /(m+L)/(m+L) := by ring,
   rw h3 at h2, clear h3,
   have h3 : 2*m*L* 2 /(m+L)/(m+L) = 4*m*L /(m+L)/(m+L) := by ring,
   rw h3 at h2, clear h3,

   have h3 : 4*m*L /(m+L)/(m+L) = 4*m*L /((m+L)*(m+L)) 
      := div_div_eq_div_mul (4 * m * L) (m + L) (m + L),
   rw h3 at h2, clear h3,

   have h3 : 4*m*L /((m+L)*(m+L)) = 4*m*L /((m+L)^2),
      rw ← pow_two,
   rw h3 at h2, clear h3,
   have h3 : 1 - 2 * m * L * η / (m + L) ≥ 1 -  4 * m * L / (m + L) ^ 2 
      := by linarith,
   clear h2,

   have h2 : (m + L) ^ 2 ≠ 0 := pow_ne_zero 2 hmL,
   have h2_2 : 1 = (m + L) ^ 2 / (m + L) ^ 2 := by exact (div_self h2).symm,

   have h2_3 : 1 -  4 * m * L / (m + L) ^ 2 = 
               (m + L) ^ 2 / (m + L) ^ 2 -  4 * m * L / (m + L) ^ 2
     := by linarith,
   rw h2_3 at h3,
   clear h2, clear h2_2, clear h2_3,

   have h2 : (m + L) ^ 2 / (m + L) ^ 2 -  4 * m * L / (m + L) ^ 2
          = ((m + L) ^ 2 -  4 * m * L) / (m + L) ^ 2
          := div_sub_div_same ((m + L) ^ 2) (4 * m * L) ((m + L) ^ 2),
   
   rw h2 at h3, clear h2,
   have h2 : (m + L) ^ 2 -  4 * m * L = m^2 + 2*m*L+L^2 - 4*m*L := by ring,
   rw h2 at h3, clear h2,

   have h2 : m^2 + 2*m*L+L^2 - 4*m*L  = m^2 - 2*m*L + L^2 := by ring,

   rw h2 at h3, clear h2,

   have h2 : m^2 - 2*m*L + L^2 = (m-L)^2 := by ring,

   rw h2 at h3, clear h2,

   have h2 : (m - L) ^ 2 / (m + L) ^ 2 = ((m - L) / (m + L) )^ 2 
      := by exact (div_pow (m - L) (m + L) 2).symm,
   
   rw h2 at h3, clear h2,

   have h2 : ((m - L) / (m + L) )^ 2 ≥ 0 := sq_nonneg ((m - L) / (m + L)),

   have h4 : 1 - 2 * m * L * η / (m + L) ≥ 0 := by linarith,
   clear h2, clear h3,

   have h4_1 : 1 - 2 * m * L * η / (m + L)
          = 1 - 2 * η * m * L / (m + L) := by ring,
   
   rw h4_1 at h4, clear h4_1,

   have h5 : (1 - 2 * η * m * L / (m + L)) * ∥grad_descent η x0 gradf k - xstar∥^ 2
    ≤ (1 - 2 * η * m * L / (m + L))*((1 - 2 * η * m * L / (m + L)) ^ k * ∥x0 - xstar∥ ^ 2)
    := by exact mul_le_mul_of_nonneg_left hk h4,
    clear h4,

   have h5_1 : (1 - 2 * η * m * L / (m + L))*((1 - 2 * η * m * L / (m + L)) ^ k * ∥x0 - xstar∥^ 2)
      = 
      (1 - 2 * η * m * L / (m + L))*(1 - 2 * η * m * L / (m + L)) ^ k * ∥x0 - xstar∥^ 2
      := by ring,
   rw h5_1 at h5,
   clear h5_1,

   linarith,

end 