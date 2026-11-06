import Calderon.ActualTSPrincipalGreen
import Calderon.ActualHigherSZeroScalarCommutatorForm
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalSymmetricFirstForm
open PrincipalCommutator ReferenceDensityBounds ActualHigherSScalarCommutatorForm
  ActualHigherSScalarCommutatorCoefficients ActualTSPrincipalGreen
  ActualHigherSZeroScalarCommutatorForm
variable {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exact principal first-form cancellation, using only the gained first forms and two principal lower rows. -/
theorem principal_firstForm_eq_symmetric_gained_and_lower
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A At C Ct : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x=0)
    (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (hAt : ∀ x ∈ K, ContDiffAt ℝ ∞ At x)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (hCt : ∀ x ∈ K, ContDiffAt ℝ ∞ Ct x)
    (hAdj : ∀ x ∈ K, ∀ u1 u2, P u1 (At x u2)=P u2 (A x u1))
    (hCadj : ∀ x ∈ K, ∀ u1 u2, P u1 (Ct x u2)=P u2 (C x u1))
    (hSym : ∀ x ∈ K, A x+At x=C x+Ct x) (X Y : R3) :
    firstForm P mu u A X Y =
      (firstForm P mu u C X Y+firstForm P mu u C Y X)/2+
      (lowerForm P mu u A Y X-lowerForm P mu u A X Y)/2 := by
  have hs := firstForm_symmetric_sum P mu u A At C Ct K hK hm.continuous hu h0 hA hAt hC hCt hSym X Y
  have ha := firstForm_sub_adjoint P mu u A At K hK hm hu h0 hA hAdj X Y
  have hc := firstForm_adjoint_swap P mu u C Ct K hK.isClosed h0 hCadj X Y
  linarith only [hs,ha,hc]

/-- Only the original beta-inverse included gradient sum is needed for two coordinate derivatives. -/
lemma included_gradient_product_le (I : E →L[ℝ] G) (beta : ℝ) (u : R3 → E)
    (x : R3) (hb : 0 < beta) (i j : Fin 3) :
    beta⁻¹*(‖I (directionalFDeriv (coordinateDirection i) u x)‖*
      ‖I (directionalFDeriv (coordinateDirection j) u x)‖) ≤ inclusionEnergyDensity I beta u x := by
  have hi := Finset.single_le_sum
    (f := fun k : Fin 3 => ‖I (directionalFDeriv (coordinateDirection k) u x)‖^2)
    (fun k _ => sq_nonneg ‖I (directionalFDeriv (coordinateDirection k) u x)‖) (Finset.mem_univ i)
  have hj := Finset.single_le_sum
    (f := fun k : Fin 3 => ‖I (directionalFDeriv (coordinateDirection k) u x)‖^2)
    (fun k _ => sq_nonneg ‖I (directionalFDeriv (coordinateDirection k) u x)‖) (Finset.mem_univ j)
  have hp : ‖I (directionalFDeriv (coordinateDirection i) u x)‖*
      ‖I (directionalFDeriv (coordinateDirection j) u x)‖ ≤
      ∑ k : Fin 3, ‖I (directionalFDeriv (coordinateDirection k) u x)‖^2 := by
    nlinarith only [hi,hj,sq_nonneg (‖I (directionalFDeriv (coordinateDirection i) u x)‖-
      ‖I (directionalFDeriv (coordinateDirection j) u x)‖)]
  exact (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hb.le)).trans
    (le_add_of_nonneg_right (mul_nonneg hb.le (sq_nonneg ‖u x‖)))

/-- A support-local coefficient graph rewrites the original gained first form using the original inclusion. -/
lemma included_firstForm_eq
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (mu : R3 → ℝ) (u : R3 → E)
    (C : R3 → E →L[ℝ] F) (Clow : R3 → G →L[ℝ] F)
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x=0)
    (hgraph : ∀ x ∈ K, C x=(Clow x).comp I) (X Y : R3) :
    firstForm (P.comp I) mu u C X Y=firstForm P mu (fun x => I (u x)) Clow X Y := by
  let v : R3 → G := fun x => I (u x)
  have hv0 : ∀ x ∉ K, v x=0 := fun x hx => by simp only [v,h0 x hx,map_zero]
  unfold firstForm
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change mu x*P (I (directionalFDeriv X u x)) (C x (directionalFDeriv Y u x)) =
    mu x*P (directionalFDeriv X v x) (Clow x (directionalFDeriv Y v x))
  by_cases hx : x ∈ K
  · change _ = mu x*P (directionalFDeriv X (fun y => I (u y)) x)
      (Clow x (directionalFDeriv Y (fun y => I (u y)) x))
    rw [hgraph x hx,ContinuousLinearMap.comp_apply,
      ActualHigherSZeroScalarCommutatorForm.directional_linear_input I u hu X x,
      ActualHigherSZeroScalarCommutatorForm.directional_linear_input I u hu Y x]
  · simp only [directional_eq_zero_off u K hK h0 X x hx,
      directional_eq_zero_off u K hK h0 Y x hx,
      directional_eq_zero_off v K hK hv0 X x hx,
      directional_eq_zero_off v K hK hv0 Y x hx,map_zero,zero_apply,mul_zero]

/-- The gained low first form is small in exactly the original high-mass/included-gradient energy. -/
theorem gained_firstForm_bound
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (mu beta : R3 → ℝ) (u : R3 → E)
    (C : R3 → G →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : Continuous mu) (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x=0)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x)
    (Q eta : ℝ) (hQ : 0 ≤ Q) (heta : 0 ≤ eta) (hmu : ∀ x, 0 ≤ mu x)
    (hC0 : ∀ x ∈ K, ‖C x‖ ≤ Q*eta/beta x) (i j : Fin 3) :
    |firstForm P mu (fun x => I (u x)) C (coordinateDirection i) (coordinateDirection j)| ≤
      (‖P‖*Q*eta)*inclusionEnergy I mu beta u := by
  let v : R3 → G := fun x => I (u x)
  have hv : ContDiff ℝ ∞ v := contDiff_const.clm_apply hu
  have hv0 : ∀ x ∉ K, v x=0 := fun x hx => by simp only [v,h0 x hx,map_zero]
  let f : R3 → ℝ := fun x => mu x*P (directionalFDeriv (coordinateDirection i) v x)
    (C x (directionalFDeriv (coordinateDirection j) v x))
  have hi : Integrable f := firstForm_integrable P mu v C K hK hm hv hv0 hC _ _
  have he := inclusionEnergy_integrable I mu beta u K hK hm hbcont (fun x => (hbpos x).ne') hu h0
  let B : ℝ := ‖P‖*Q*eta
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hPt (x : R3) : |f x| ≤ B*(mu x*inclusionEnergyDensity I (beta x) u x) := by
    have hmux : 0 ≤ mu x := hmu x
    by_cases hx : x ∈ K
    · change |mu x*P (directionalFDeriv (coordinateDirection i) (fun y => I (u y)) x)
        (C x (directionalFDeriv (coordinateDirection j) (fun y => I (u y)) x))| ≤ _
      rw [abs_mul,abs_of_nonneg (hmu x),
        ActualHigherSZeroScalarCommutatorForm.directional_linear_input I u hu (coordinateDirection i) x,
        ActualHigherSZeroScalarCommutatorForm.directional_linear_input I u hu (coordinateDirection j) x]
      calc
        _ ≤ mu x*(‖P‖*‖C x‖*(‖I (directionalFDeriv (coordinateDirection i) u x)‖*
            ‖I (directionalFDeriv (coordinateDirection j) u x)‖)) :=
          mul_le_mul_of_nonneg_left (abs_operator_pair_general P (C x) _ _) (hmu x)
        _ ≤ mu x*(‖P‖*(Q*eta/beta x)*(‖I (directionalFDeriv (coordinateDirection i) u x)‖*
            ‖I (directionalFDeriv (coordinateDirection j) u x)‖)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC0 x hx) (norm_nonneg P))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hmux
        _ = (‖P‖*Q*eta*mu x)*((beta x)⁻¹*(‖I (directionalFDeriv (coordinateDirection i) u x)‖*
            ‖I (directionalFDeriv (coordinateDirection j) u x)‖)) := by rw [div_eq_mul_inv]; ring
        _ ≤ (‖P‖*Q*eta*mu x)*inclusionEnergyDensity I (beta x) u x :=
          mul_le_mul_of_nonneg_left (included_gradient_product_le I (beta x) u x (hbpos x) i j) (by positivity)
        _ = B*(mu x*inclusionEnergyDensity I (beta x) u x) := by dsimp [B]; ring
    · have hz : f x=0 := by
        simp only [f,directional_eq_zero_off v K hK.isClosed hv0 (coordinateDirection i) x hx,
          directional_eq_zero_off v K hK.isClosed hv0 (coordinateDirection j) x hx,map_zero,zero_apply,mul_zero]
      rw [hz,abs_zero]
      exact mul_nonneg hB (mul_nonneg (hmu x) (inclusionEnergyDensity_nonneg I _ u x (hbpos x).le))
  change |∫ x, f x| ≤ B*inclusionEnergy I mu beta u
  calc
    _ ≤ ∫ x, |f x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, B*(mu x*inclusionEnergyDensity I (beta x) u x) := integral_mono hi.abs (he.const_mul B) hPt
    _ = B*inclusionEnergy I mu beta u := by rw [integral_const_mul]; rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalSymmetricFirstForm
