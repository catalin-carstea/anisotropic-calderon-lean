import Calderon.ActualTSPrincipalGreen

/-! Exact weighted symmetric first-form Green identity and mass-energy bound.
The statements are generic; they are not specialized to the original207-word coefficients. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSymmetricFirstGreen
open PrincipalCommutator ActualHigherSScalarCommutatorForm ActualHigherSScalarCommutatorCoefficients
  ReferenceDensityBounds

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def symmetricFirstDensity (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ)
    (u : R3 → E) (A : R3 → E →L[ℝ] F) (X : R3) (x : R3) : ℝ :=
  mu x*(P (directionalFDeriv X u x) (A x (u x))+
    P (u x) (A x (directionalFDeriv X u x)))

def diagonalLowerDensity (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ)
    (u : R3 → E) (A : R3 → E →L[ℝ] F) (X : R3) (x : R3) : ℝ :=
  directionalFDeriv X mu x*P (u x) (A x (u x))+
    mu x*P (u x) ((directionalFDeriv X A x) (u x))

/-- Every integral exists before the literal symmetric first-form identity is used. -/
theorem symmetric_first_integral_identity
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x=0) (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (X : R3) :
    Integrable (symmetricFirstDensity P mu u A X) ∧
    Integrable (diagonalLowerDensity P mu u A X) ∧
    (∫ x, symmetricFirstDensity P mu u A X x)=
      -(∫ x, diagonalLowerDensity P mu u A X x) := by
  let du := directionalFDeriv X u
  have hdu : ContDiff ℝ ∞ du := contDiff_directionalFDeriv X u hu
  have hdu0 : ∀ x ∉ K, du x=0 :=
    fun x hx => directional_eq_zero_off u K hK.isClosed h0 X x hx
  have hDA : ∀ x ∈ K, ContDiffAt ℝ ∞ (directionalFDeriv X A) x :=
    fun x hx => contDiffAt_directional A x X (hA x hx)
  let f0 : R3 → ℝ := fun x => directionalFDeriv X mu x*P (u x) (A x (u x))
  let f1 : R3 → ℝ := fun x => mu x*P (du x) (A x (u x))
  let f2 : R3 → ℝ := fun x => mu x*P (u x) ((directionalFDeriv X A x) (u x))
  let f3 : R3 → ℝ := fun x => mu x*P (u x) (A x (du x))
  have hi0 : Integrable f0 :=
    integrable_weighted_supported_operator_pair P (directionalFDeriv X mu) u u A K hK
      (contDiff_directionalFDeriv X mu hm).continuous hu.continuous hu h0 hA
  have hi1 : Integrable f1 :=
    integrable_weighted_supported_operator_pair P mu du u A K hK hm.continuous hdu.continuous hu h0 hA
  have hi2 : Integrable f2 :=
    integrable_weighted_supported_operator_pair P mu u u (directionalFDeriv X A) K hK
      hm.continuous hu.continuous hu h0 hDA
  have hi3 : Integrable f3 :=
    integrable_weighted_supported_operator_pair P mu u du A K hK hm.continuous hu.continuous hdu hdu0 hA
  let z : R3 → F := fun x => A x (u x)
  let f : R3 → E := fun x => mu x • u x
  have hz : ContDiff ℝ ∞ z := contDiff_supported_operator_apply u A K hK.isClosed hu h0 hA
  have hzc : HasCompactSupport z := compact_supported_operator_apply u A K hK h0
  have hf : ContDiff ℝ ∞ f := hm.smul hu
  have hfi : Integrable (fun x => P (directionalFDeriv X f x) (z x)) :=
    compact_bilinear_integrable P _ _ (contDiff_directionalFDeriv X f hf).continuous hz.continuous hzc
  have hzi : Integrable (fun x => P (f x) (directionalFDeriv X z x)) :=
    compact_bilinear_integrable P _ _ hf.continuous (contDiff_directionalFDeriv X z hz).continuous
      (hzc.fderiv_apply (𝕜 := ℝ) X)
  have hbase : Integrable (fun x => P (f x) (z x)) :=
    compact_bilinear_integrable P _ _ hf.continuous hz.continuous hzc
  have hg := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := P) (v := X) hfi hzi hbase
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hz.differentiable (by simp) x)
  have hzD (x : R3) : directionalFDeriv X z x =
      directionalFDeriv X A x (u x)+A x (directionalFDeriv X u x) :=
    directional_operator_apply_supported u A K hK.isClosed hu h0 hA X x
  have hfD (x : R3) : directionalFDeriv X f x =
      directionalFDeriv X mu x • u x+mu x • directionalFDeriv X u x :=
    directional_smul_at mu u x X hm.contDiffAt hu.contDiffAt
  have hLeft : (fun x => P (f x) (directionalFDeriv X z x))=(fun x => f2 x+f3 x) := by
    funext x
    rw [hzD x]
    simp only [f,f2,f3,du,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,map_add,mul_add]
  have hRight : (fun x => P (directionalFDeriv X f x) (z x))=(fun x => f0 x+f1 x) := by
    funext x
    rw [hfD x]
    simp only [f0,f1,z,du,map_add,map_smul,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul]
  change (∫ x, P (f x) (directionalFDeriv X z x))=
    -(∫ x, P (directionalFDeriv X f x) (z x)) at hg
  rw [hLeft,hRight,integral_add hi2 hi3,integral_add hi0 hi1] at hg
  have hS : symmetricFirstDensity P mu u A X=(fun x => f1 x+f3 x) := by
    funext x
    simp only [symmetricFirstDensity,f1,f3,du,mul_add]
  have hR : diagonalLowerDensity P mu u A X=(fun x => f0 x+f2 x) := rfl
  refine ⟨hS.symm ▸ (hi1.add hi3),hR.symm ▸ (hi0.add hi2),?_⟩
  rw [hS,hR,integral_add hi1 hi3,integral_add hi0 hi2]
  linarith only [hg]

private lemma diagonal_action_bound (P : E →L[ℝ] F →L[ℝ] ℝ) (A : E →L[ℝ] F)
    (u : E) (B : ℝ) (hB : 0 ≤ B) (hA : ‖A‖ ≤ B) :
    |P u (A u)| ≤ ‖P‖*B*‖u‖^2 := by
  have hAv : ‖A u‖ ≤ B*‖u‖ :=
    (A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hPair : |P u (A u)| ≤ ‖P‖*‖u‖*‖A u‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm₂ P u (A u)
  exact (hPair.trans (mul_le_mul_of_nonneg_left hAv (mul_nonneg (ContinuousLinearMap.opNorm_nonneg P) (norm_nonneg u)))).trans_eq
    (by ring)

/-- Quantitative symmetric first-form bound uses genuine weighted mass energy only.
The statement is generic; coefficient caps enter as hypotheses. -/
theorem symmetric_first_integral_mass_bound
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu beta : R3 → ℝ) (u : R3 → E)
    (A : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hb : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x=0)
    (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (X : R3)
    (Q M eta : ℝ) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hmu : ∀ x, 0 ≤ mu x)
    (hA0 : ∀ x ∈ K, ‖A x‖ ≤ Q*eta*beta x)
    (hA1 : ∀ x ∈ K, ‖directionalFDeriv X A x‖ ≤ Q*eta*beta x)
    (hdmu : ∀ x ∈ K, |directionalFDeriv X mu x| ≤ M*mu x) :
    Integrable (symmetricFirstDensity P mu u A X) ∧
      |∫ x, symmetricFirstDensity P mu u A X x| ≤
        (‖P‖*Q*(M+1)*eta)*(∫ x, mu x*beta x*‖u x‖^2) := by
  have hGreen := symmetric_first_integral_identity P mu u A K hK hm hu h0 hA X
  let e : R3 → ℝ := fun x => mu x*beta x*‖u x‖^2
  let B : ℝ := ‖P‖*Q*(M+1)*eta
  have hP0 : 0 ≤ ‖P‖ := ContinuousLinearMap.opNorm_nonneg P
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have heCont : Continuous e := (hm.continuous.mul hb).mul (hu.continuous.norm.pow 2)
  have heCompact : HasCompactSupport e := HasCompactSupport.intro hK (by
    intro x hx
    simp only [e,h0 x hx,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero])
  have heI : Integrable e := heCont.integrable_of_hasCompactSupport heCompact
  have hPoint (x : R3) : |diagonalLowerDensity P mu u A X x| ≤ B*e x := by
    by_cases hx : x ∈ K
    · have hBeta0 : 0 ≤ beta x := (hbpos x).le
      have hCx := diagonal_action_bound P (A x) (u x) (Q*eta*beta x) (by positivity) (hA0 x hx)
      have hDx := diagonal_action_bound P (directionalFDeriv X A x) (u x)
        (Q*eta*beta x) (by positivity) (hA1 x hx)
      have h0B : 0 ≤ ‖P‖*(Q*eta*beta x)*‖u x‖^2 := by positivity
      have hTerm0 : |directionalFDeriv X mu x*P (u x) (A x (u x))| ≤
          (M*mu x)*(‖P‖*(Q*eta*beta x)*‖u x‖^2) := by
        rw [abs_mul]
        exact mul_le_mul (hdmu x hx) hCx (abs_nonneg _) (mul_nonneg hM (hmu x))
      have hTerm1 : |mu x*P (u x) ((directionalFDeriv X A x) (u x))| ≤
          mu x*(‖P‖*(Q*eta*beta x)*‖u x‖^2) := by
        rw [abs_mul,abs_of_nonneg (hmu x)]
        exact mul_le_mul_of_nonneg_left hDx (hmu x)
      have hAbs : |diagonalLowerDensity P mu u A X x| ≤
          |directionalFDeriv X mu x*P (u x) (A x (u x))|+
            |mu x*P (u x) ((directionalFDeriv X A x) (u x))| := by
        simpa only [diagonalLowerDensity,Real.norm_eq_abs] using norm_add_le
          (directionalFDeriv X mu x*P (u x) (A x (u x)))
          (mu x*P (u x) ((directionalFDeriv X A x) (u x)))
      exact (hAbs.trans (add_le_add hTerm0 hTerm1)).trans_eq (by dsimp only [B,e]; ring)
    · simp only [diagonalLowerDensity,h0 x hx,map_zero,zero_apply,mul_zero,add_zero,abs_zero,
        e,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0)]
      exact le_refl 0
  have hNormPoint (x : R3) : ‖diagonalLowerDensity P mu u A X x‖ ≤ B*e x := by
    simpa only [Real.norm_eq_abs] using hPoint x
  have hMono := integral_mono hGreen.2.1.norm (heI.const_mul B) hNormPoint
  rw [integral_const_mul] at hMono
  refine ⟨hGreen.1,?_⟩
  calc
    _ = |∫ x, diagonalLowerDensity P mu u A X x| := by rw [hGreen.2.2,abs_neg]
    _ ≤ ∫ x, ‖diagonalLowerDensity P mu u A X x‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => diagonalLowerDensity P mu u A X x)
    _ ≤ B*∫ x, e x := hMono

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSymmetricFirstGreen
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSymmetricFirstGreen.symmetric_first_integral_identity
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSymmetricFirstGreen.symmetric_first_integral_mass_bound
