import Calderon.ActualTSPrincipalGreen
import Calderon.ActualHigherSZeroScalarCommutatorForm
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPairedLowerGreenBound
open PrincipalCommutator ReferenceDensityBounds ActualHigherSScalarCommutatorForm
  ActualHigherSScalarCommutatorCoefficients ActualTSPrincipalGreen ActualHigherSZeroScalarCommutatorForm
variable {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiation of a coefficient pairing with two fixed angular inputs. -/
lemma directional_coefficient_pair
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (A : R3 → E →L[ℝ] F)
    (x X : R3) (hA : ContDiffAt ℝ ∞ A x) (u v : E) :
    directionalFDeriv X (fun y => P (I v) (A y u)) x =
      P (I v) ((directionalFDeriv X A x) u) := by
  have hAd : DifferentiableAt ℝ A x := hA.differentiableAt (by simp)
  have hAu : DifferentiableAt ℝ (fun y => A y u) x := hAd.clm_apply (differentiableAt_const u)
  unfold directionalFDeriv
  rw [fderiv_clm_apply (differentiableAt_const (P (I v))) hAu]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,fderiv_const_apply,zero_apply,map_zero,add_zero,zero_add]
  rw [fderiv_clm_apply hAd (differentiableAt_const u)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,fderiv_const_apply,zero_apply,map_zero,add_zero,zero_add]

/-- Actual neighborhood pairing, rather than membership at a closed support point, justifies the derivative transpose. -/
theorem paired_directional_coefficient
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G)
    (A At : R3 → E →L[ℝ] F) (x X : R3)
    (hA : ContDiffAt ℝ ∞ A x) (hAt : ContDiffAt ℝ ∞ At x)
    (hpair : ∀ᶠ y in 𝓝 x, ∀ u v : E, P (I v) (A y u)=P (I u) (At y v))
    (u v : E) :
    P (I v) ((directionalFDeriv X A x) u)=P (I u) ((directionalFDeriv X At x) v) := by
  have he : (fun y => P (I v) (A y u)) =ᶠ[𝓝 x] (fun y => P (I u) (At y v)) :=
    hpair.mono (fun y hy => hy u v)
  have hd := congrArg (fun T : R3 →L[ℝ] ℝ => T X) (he.fderiv_eq (𝕜 := ℝ))
  change directionalFDeriv X (fun y => P (I v) (A y u)) x =
    directionalFDeriv X (fun y => P (I u) (At y v)) x at hd
  rw [directional_coefficient_pair P I A x X hA u v,
    directional_coefficient_pair P I At x X hAt v u] at hd
  exact hd

/-- The principal lower Green row uses only high mass and the original included first derivative. -/
theorem paired_lowerForm_bound
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G)
    (mu beta : R3 → ℝ) (u : R3 → E) (A At : R3 → E →L[ℝ] F)
    (K : Set R3) (hK : IsCompact K) (hm : ContDiff ℝ ∞ mu)
    (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x=0)
    (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (hAt : ∀ x ∈ K, ContDiffAt ℝ ∞ At x)
    (hpair : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, ∀ v w : E, P (I v) (A y w)=P (I w) (At y v))
    (Q M eta : ℝ) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hmu : ∀ x, 0 ≤ mu x) (i j : Fin 3)
    (hAt0 : ∀ x ∈ K, ‖At x‖ ≤ Q*eta)
    (hAt1 : ∀ x ∈ K, ‖directionalFDeriv (coordinateDirection i) At x‖ ≤ Q*eta)
    (hdmu : ∀ x ∈ K, |directionalFDeriv (coordinateDirection i) mu x| ≤ M*mu x) :
    Integrable (fun x => directionalFDeriv (coordinateDirection i) mu x*P (I (u x))
      (A x (directionalFDeriv (coordinateDirection j) u x))+
      mu x*P (I (u x)) ((directionalFDeriv (coordinateDirection i) A x)
        (directionalFDeriv (coordinateDirection j) u x))) ∧
    |lowerForm (P.comp I) mu u A (coordinateDirection i) (coordinateDirection j)| ≤
      (‖P‖*Q*(M+1)*eta)*inclusionEnergy I mu beta u := by
  let R : R3 → ℝ := fun x => directionalFDeriv (coordinateDirection i) mu x*P (I (u x))
      (A x (directionalFDeriv (coordinateDirection j) u x))+
      mu x*P (I (u x)) ((directionalFDeriv (coordinateDirection i) A x)
        (directionalFDeriv (coordinateDirection j) u x))
  have hi : Integrable R := lowerForm_integrable (P.comp I) mu u A K hK hm hu h0 hA _ _
  have he := inclusionEnergy_integrable I mu beta u K hK hm.continuous hbcont
    (fun x => (hbpos x).ne') hu h0
  let B : ℝ := ‖P‖*Q*(M+1)*eta
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound (x : R3) : |R x| ≤ B*(mu x*inclusionEnergyDensity I (beta x) u x) := by
    by_cases hx : x ∈ K
    · have hp := (hpair x hx).self_of_nhds
      have hp0 : P (I (u x)) (A x (directionalFDeriv (coordinateDirection j) u x))=
          P (I (directionalFDeriv (coordinateDirection j) u x)) (At x (u x)) := hp _ _
      have hp1 := paired_directional_coefficient P I A At x (coordinateDirection i)
        (hA x hx) (hAt x hx) ((hpair x hx).mono (fun y hy a b => hy b a))
        (directionalFDeriv (coordinateDirection j) u x) (u x)
      have hMixed := inclusion_energy_mixed_le I (beta x) u x (hbpos x) j
      have hCap0 : |P (I (directionalFDeriv (coordinateDirection j) u x)) (At x (u x))| ≤
          ‖P‖*(Q*eta)*inclusionEnergyDensity I (beta x) u x := by
        apply (abs_operator_pair_general P (At x) _ _).trans
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hAt0 x hx) (norm_nonneg P))
          hMixed (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      have hCap1 : |P (I (directionalFDeriv (coordinateDirection j) u x))
          ((directionalFDeriv (coordinateDirection i) At x) (u x))| ≤
          ‖P‖*(Q*eta)*inclusionEnergyDensity I (beta x) u x := by
        apply (abs_operator_pair_general P _ _ _).trans
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hAt1 x hx) (norm_nonneg P))
          hMixed (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      have h1 : |directionalFDeriv (coordinateDirection i) mu x*
          P (I (u x)) (A x (directionalFDeriv (coordinateDirection j) u x))| ≤
          M*mu x*(‖P‖*(Q*eta)*inclusionEnergyDensity I (beta x) u x) := by
        rw [hp0,abs_mul]
        exact mul_le_mul (hdmu x hx) hCap0 (abs_nonneg _) (mul_nonneg hM (hmu x))
      have h2 : |mu x*P (I (u x)) ((directionalFDeriv (coordinateDirection i) A x)
          (directionalFDeriv (coordinateDirection j) u x))| ≤
          mu x*(‖P‖*(Q*eta)*inclusionEnergyDensity I (beta x) u x) := by
        rw [hp1,abs_mul,abs_of_nonneg (hmu x)]
        exact mul_le_mul_of_nonneg_left hCap1 (hmu x)
      calc
        |R x| ≤ |directionalFDeriv (coordinateDirection i) mu x*
            P (I (u x)) (A x (directionalFDeriv (coordinateDirection j) u x))|+
            |mu x*P (I (u x)) ((directionalFDeriv (coordinateDirection i) A x)
              (directionalFDeriv (coordinateDirection j) u x))| := abs_add_le _ _
        _ ≤ M*mu x*(‖P‖*(Q*eta)*inclusionEnergyDensity I (beta x) u x)+
            mu x*(‖P‖*(Q*eta)*inclusionEnergyDensity I (beta x) u x) := add_le_add h1 h2
        _ = B*(mu x*inclusionEnergyDensity I (beta x) u x) := by dsimp [B]; ring
    · have hr : R x=0 := by simp only [R,h0 x hx,map_zero,zero_apply,mul_zero,add_zero]
      rw [hr,abs_zero]
      exact mul_nonneg hB (mul_nonneg (hmu x) (inclusionEnergyDensity_nonneg I (beta x) u x (hbpos x).le))
  refine ⟨hi,?_⟩
  change |∫ x, R x| ≤ B*inclusionEnergy I mu beta u
  calc
    |∫ x, R x| ≤ ∫ x, |R x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, B*(mu x*inclusionEnergyDensity I (beta x) u x) :=
      integral_mono_ae hi.abs (he.const_mul B) (Filter.Eventually.of_forall hbound)
    _ = B*inclusionEnergy I mu beta u := by rw [integral_const_mul]; rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPairedLowerGreenBound
