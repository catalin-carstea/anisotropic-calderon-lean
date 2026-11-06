import Calderon.SmoothSobolevBridge
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section
open Function
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily

/-- The actual finite uniform derivative fields, including the coefficient itself. -/
abbrev CoefficientJetSpace (r : ℕ) :=
  (j : Fin (r + 1)) →
    BoundedContinuousFunction R3 (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => R3) ℝ)

instance (priority := 2000) instNormedAddCommGroupCoefficientJetSpace (r : ℕ) :
    NormedAddCommGroup (CoefficientJetSpace r) := by
  letI : ∀ j : Fin (r + 1), NormedAddCommGroup
      (BoundedContinuousFunction R3
        (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => R3) ℝ)) := fun _ => inferInstance
  unfold CoefficientJetSpace
  infer_instance

instance (priority := 2000) instNormedSpaceCoefficientJetSpace (r : ℕ) :
    NormedSpace ℝ (CoefficientJetSpace r) := by
  letI : ∀ j : Fin (r + 1), NormedSpace ℝ
      (BoundedContinuousFunction R3
        (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => R3) ℝ)) := fun _ => inferInstance
  unfold CoefficientJetSpace
  infer_instance

instance instContinuousAddCoefficientJetFields (r : ℕ) :
    ∀ j : Fin (r + 1),
      ContinuousAdd (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => R3) ℝ) :=
  fun _ => inferInstance

/-- Jets of globally smooth compactly supported coefficients, with the finite uniform norm. -/
def smoothCoefficientJetSubmodule (r : ℕ) : Submodule ℝ (CoefficientJetSpace r) where
  carrier := {F | ∃ phi : R3 → ℝ, ContDiff ℝ ∞ phi ∧ HasCompactSupport phi ∧
    ∀ (j : Fin (r + 1)) (x : R3), F j x = iteratedFDeriv ℝ j.val phi x}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    intro j x
    simpa using (iteratedFDeriv_const_smul_apply (a := (0 : ℝ))
      (show ContDiffAt ℝ j.val (0 : R3 → ℝ) x from contDiff_const.contDiffAt)).symm
  add_mem' := by
    rintro F G ⟨phi, hp, hpc, hF⟩ ⟨psi, hq, hqc, hG⟩
    refine ⟨phi + psi, hp.add hq, hpc.add hqc, ?_⟩
    intro j x
    change F j x + G j x = iteratedFDeriv ℝ j.val (phi + psi) x
    rw [hF, hG]
    exact (iteratedFDeriv_add_apply
      ((hp.of_le (by simp)).contDiffAt) ((hq.of_le (by simp)).contDiffAt)).symm
  smul_mem' := by
    rintro c F ⟨phi, hp, hpc, hF⟩
    refine ⟨c • phi, contDiff_const.smul hp, hpc.smul_left, ?_⟩
    intro j x
    change c • F j x = iteratedFDeriv ℝ j.val (c • phi) x
    rw [hF]
    exact (iteratedFDeriv_const_smul_apply ((hp.of_le (by simp)).contDiffAt)).symm

abbrev SmoothCoefficientJets (r : ℕ) := ↥(smoothCoefficientJetSubmodule r)

/-- Zeroth derivative evaluation recovers the actual scalar coefficient. -/
def coefficientValue (r : ℕ) (F : SmoothCoefficientJets r) (x : R3) : ℝ :=
  F.1 ⟨0, Nat.zero_lt_succ r⟩ x (fun i => Fin.elim0 i)

theorem coefficientValue_eq (r : ℕ) (F : SmoothCoefficientJets r)
    (phi : R3 → ℝ)
    (hF : ∀ (j : Fin (r + 1)) (x : R3), F.1 j x = iteratedFDeriv ℝ j.val phi x) :
    coefficientValue r F = phi := by
  funext x
  unfold coefficientValue
  rw [hF]
  exact iteratedFDeriv_zero_apply _

theorem contDiff_coefficientValue (r : ℕ) (F : SmoothCoefficientJets r) :
    ContDiff ℝ ∞ (coefficientValue r F) := by
  obtain ⟨phi, hp, _, hF⟩ := F.2
  rw [coefficientValue_eq r F phi hF]
  exact hp

theorem hasCompactSupport_coefficientValue (r : ℕ) (F : SmoothCoefficientJets r) :
    HasCompactSupport (coefficientValue r F) := by
  obtain ⟨phi, _, hc, hF⟩ := F.2
  rw [coefficientValue_eq r F phi hF]
  exact hc

theorem coefficientJet_eq_iteratedFDeriv (r : ℕ) (F : SmoothCoefficientJets r)
    (j : Fin (r + 1)) (x : R3) :
    F.1 j x = iteratedFDeriv ℝ j.val (coefficientValue r F) x := by
  obtain ⟨phi, _, _, hF⟩ := F.2
  rw [coefficientValue_eq r F phi hF]
  exact hF j x

theorem norm_iteratedFDeriv_coefficientValue_le (r : ℕ) (F : SmoothCoefficientJets r)
    (j : ℕ) (hj : j ≤ r) (x : R3) :
    ‖iteratedFDeriv ℝ j (coefficientValue r F) x‖ ≤ ‖F‖ := by
  let i : Fin (r + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  rw [← coefficientJet_eq_iteratedFDeriv r F i x]
  exact ((F.1 i).norm_coe_le_norm x).trans (norm_le_pi_norm F.1 i)

theorem coefficientValue_add (r : ℕ) (F G : SmoothCoefficientJets r) :
    coefficientValue r (F + G) = coefficientValue r F + coefficientValue r G := by
  ext x
  rfl

theorem coefficientValue_smul (r : ℕ) (c : ℝ) (F : SmoothCoefficientJets r) :
    coefficientValue r (c • F) = c • coefficientValue r F := by
  ext x
  rfl

/-- Actual derivative fields of every smooth compactly supported coefficient. -/
def compactCoefficientJet (r : ℕ) (phi : R3 → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) : CoefficientJetSpace r :=
  let M := Classical.choose (hc.exists_bound_iteratedFDeriv hp r)
  let hM := Classical.choose_spec (hc.exists_bound_iteratedFDeriv hp r)
  fun j => BoundedContinuousFunction.mkOfBound
    ⟨iteratedFDeriv ℝ j.val phi, hp.continuous_iteratedFDeriv (by simp)⟩ (2 * M)
    (fun x y => by
      have hj : j.val ≤ r := Nat.le_of_lt_succ j.isLt
      calc
        dist (iteratedFDeriv ℝ j.val phi x) (iteratedFDeriv ℝ j.val phi y)
            ≤ ‖iteratedFDeriv ℝ j.val phi x‖ + ‖iteratedFDeriv ℝ j.val phi y‖ :=
              dist_le_norm_add_norm _ _
        _ ≤ M + M := add_le_add (hM.2 j.val hj x) (hM.2 j.val hj y)
        _ = 2 * M := by ring)

theorem compactCoefficientJet_apply (r : ℕ) (phi : R3 → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (j : Fin (r + 1)) (x : R3) :
    compactCoefficientJet r phi hp hc j x = iteratedFDeriv ℝ j.val phi x := rfl

theorem compactCoefficientJet_mem (r : ℕ) (phi : R3 → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    compactCoefficientJet r phi hp hc ∈ smoothCoefficientJetSubmodule r :=
  ⟨phi, hp, hc, fun _ _ => rfl⟩

/-- Every original smooth compact coefficient is realized in the concrete norm space. -/
def compactCoefficient (r : ℕ) (phi : R3 → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) : SmoothCoefficientJets r :=
  ⟨compactCoefficientJet r phi hp hc, compactCoefficientJet_mem r phi hp hc⟩

theorem coefficientValue_compactCoefficient (r : ℕ) (phi : R3 → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    coefficientValue r (compactCoefficient r phi hp hc) = phi := by
  funext x
  exact iteratedFDeriv_zero_apply _

end OAI.AnisotropicCalderon.DirichletFamily
