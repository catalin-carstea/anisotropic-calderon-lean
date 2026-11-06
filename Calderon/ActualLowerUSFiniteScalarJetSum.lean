import Calderon.ActualReferenceDDHigherCLMProducts
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherCLMProducts

/-- Finite scalar jet bookkeeping over one opaque normed real space. -/
theorem hasCoordinateWordJetBound_finite_scalar_sum
    {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (A : ι → E) (x : R3) (C M beta : ℝ) (s : ℕ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hb : 0 ≤ beta)
    (hA : ∀ i, ‖A i‖ ≤ M)
    (hcap : ∀ i, HasCoordinateWordJetBound N (c i) x C beta s) :
    HasCoordinateWordJetBound N (fun y => ∑ i, c i y • A i) x
      ((Fintype.card ι : ℝ)*((2:ℝ)^N*C*M)) beta s := by
  classical
  have hEach (i : ι) : HasCoordinateWordJetBound N (fun y => c i y • A i) x
      ((2:ℝ)^N*C*M) beta s := by
    have hConst := hasCoordinateWordJetBound_const_normed N (A i) x M beta (hA i) hb
    have hProd := hasCoordinateWordJetBound_smul N (c i) (fun _ : R3 => A i)
      (hc i) contDiff_const x C M beta s 0 hC hM hb (hcap i) hConst
    simpa only [Nat.add_zero] using hProd
  exact hasCoordinateWordJetBound_sum N (fun i y => c i y • A i)
    (fun i => (hc i).smul contDiff_const) x ((2:ℝ)^N*C*M) beta s hEach

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
