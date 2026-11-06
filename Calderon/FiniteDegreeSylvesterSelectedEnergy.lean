import Calderon.FiniteSylvesterHalfBound

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SpectralSylvester

/-! Full upfront: EXPANSION-v001.json. Original DEGREE target retained. Selected
Casimir energy is intermediate; auxiliary a=k+1/2 gives exact Sylvester differences.
The generic Casimir product estimate is conditional and actualCsharp is still pending. -/

lemma one_add_casimir_le_four_half_shift_sq (k : ℕ) :
    1+(k:ℝ)*((k:ℝ)+1) ≤ 4*((k:ℝ)+(1/2:ℝ))^2 := by
  nlinarith [Nat.cast_nonneg (α := ℝ) k, sq_nonneg (k:ℝ)]

lemma finite_casimir_energy_le_four_half_shift_energy
    {ι : Type*} (s : Finset ι) (degree : ι → ℕ) (x : ι → ℝ) :
    (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*x i^2) ≤
      4*(∑ i ∈ s, (((degree i:ℝ)+(1/2:ℝ))*x i)^2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ (4*((degree i:ℝ)+(1/2:ℝ))^2)*x i^2 :=
      mul_le_mul_of_nonneg_right (one_add_casimir_le_four_half_shift_sq (degree i)) (sq_nonneg _)
    _ = _ := by ring

lemma finite_degree_commutator_half_form_bound_of_casimir_product_bound
    {ι : Type*} (s : Finset ι) (degree : ι → ℕ) (K : ι → ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hCasimir : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s,
        (((degree i:ℝ)*((degree i:ℝ)+1)-(degree j:ℝ)*((degree j:ℝ)+1))*K i j*x j*y i)| ≤
      M*Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*x i^2)*
        Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*y i^2))
    (u v : ι → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, ((degree i:ℝ)-(degree j:ℝ))*K i j*u j*v i| ≤
      2*M*Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*u i^2)*
        Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*v i^2) := by
  let a (i : ι) : ℝ := (degree i:ℝ)+(1/2:ℝ)
  have ha : ∀ i ∈ s, 0 < a i := by
    intro i _
    dsimp only [a]
    positivity
  have hConv (z : ι → ℝ) :
      Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*z i^2) ≤
      2*Real.sqrt (∑ i ∈ s, (a i*z i)^2) := by
    have hEa : 0 ≤ ∑ i ∈ s, (a i*z i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hWeight : (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*z i^2) ≤
        4*(∑ i ∈ s, (a i*z i)^2) := finite_casimir_energy_le_four_half_shift_energy s degree z
    have hSquare : (2*Real.sqrt (∑ i ∈ s, (a i*z i)^2))^2 =
        4*(∑ i ∈ s, (a i*z i)^2) := by
      rw [mul_pow, Real.sq_sqrt hEa]
      ring
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hWeight.trans_eq hSquare.symm⟩
  have hD : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s, (a i^2-a j^2)*K i j*x j*y i| ≤
        ((4*M)/2)*((∑ i ∈ s, (a i*x i)^2)+(∑ i ∈ s, (a i*y i)^2)) := by
    intro x y
    let X : ℝ := ∑ i ∈ s, (a i*x i)^2
    let Y : ℝ := ∑ i ∈ s, (a i*y i)^2
    have hX : 0 ≤ X := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hY : 0 ≤ Y := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hSame : (∑ i ∈ s, ∑ j ∈ s, (a i^2-a j^2)*K i j*x j*y i) =
        ∑ i ∈ s, ∑ j ∈ s,
          (((degree i:ℝ)*((degree i:ℝ)+1)-(degree j:ℝ)*((degree j:ℝ)+1))*K i j*x j*y i) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [a]
      ring
    have hProd : Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*x i^2)*
        Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*y i^2) ≤
        (2*Real.sqrt X)*(2*Real.sqrt Y) :=
      mul_le_mul (hConv x) (hConv y) (Real.sqrt_nonneg _) (by positivity)
    have hYoung : 2*Real.sqrt X*Real.sqrt Y ≤ X+Y := by
      have hXsq := Real.sq_sqrt hX
      have hYsq := Real.sq_sqrt hY
      nlinarith [sq_nonneg (Real.sqrt X-Real.sqrt Y)]
    calc
      _ ≤ M*Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*x i^2)*
          Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*y i^2) :=
        (congrArg abs hSame).trans_le (hCasimir x y)
      _ = M*(Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*x i^2)*
          Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ)*((degree i:ℝ)+1))*y i^2)) := by ring
      _ ≤ M*((2*Real.sqrt X)*(2*Real.sqrt Y)) := mul_le_mul_of_nonneg_left hProd hM
      _ = (2*M)*(2*Real.sqrt X*Real.sqrt Y) := by ring
      _ ≤ (2*M)*(X+Y) := mul_le_mul_of_nonneg_left hYoung (by positivity)
      _ = _ := by ring
  have hHalf := finite_sylvester_half_form_bound s a ha K (4*M) (by positivity) hD u v
  have hDegree : (∑ i ∈ s, ∑ j ∈ s, (a i-a j)*K i j*u j*v i) =
      ∑ i ∈ s, ∑ j ∈ s, ((degree i:ℝ)-(degree j:ℝ))*K i j*u j*v i := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [a]
    ring
  have hPhysical (z : ι → ℝ) : Real.sqrt (∑ i ∈ s, a i*z i^2) ≤
      Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*z i^2) := by
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    dsimp only [a]
    linarith
  have hProd : Real.sqrt (∑ i ∈ s, a i*u i^2)*Real.sqrt (∑ i ∈ s, a i*v i^2) ≤
      Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*u i^2)*
        Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*v i^2) :=
    mul_le_mul (hPhysical u) (hPhysical v) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ ((4*M)/2)*Real.sqrt (∑ i ∈ s, a i*u i^2)*Real.sqrt (∑ i ∈ s, a i*v i^2) :=
      (congrArg abs hDegree).symm.trans_le hHalf
    _ = (2*M)*(Real.sqrt (∑ i ∈ s, a i*u i^2)*Real.sqrt (∑ i ∈ s, a i*v i^2)) := by ring
    _ ≤ (2*M)*(Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*u i^2)*
        Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*v i^2)) :=
      mul_le_mul_of_nonneg_left hProd (by positivity)
    _ = _ := by ring

#print axioms OAI.AnisotropicCalderon.SpectralSylvester.one_add_casimir_le_four_half_shift_sq
#print axioms OAI.AnisotropicCalderon.SpectralSylvester.finite_casimir_energy_le_four_half_shift_energy
#print axioms OAI.AnisotropicCalderon.SpectralSylvester.finite_degree_commutator_half_form_bound_of_casimir_product_bound

end OAI.AnisotropicCalderon.SpectralSylvester
