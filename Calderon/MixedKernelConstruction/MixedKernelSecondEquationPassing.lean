import Calderon.MixedKernelConstruction.MixedKernelMonotoneCurrentPair
import Calderon.MixedKernelConstruction.MixedKernelPositiveChartAgreement
import Calderon.MixedKernelConstruction.MixedKernelObservedOutputRooms
import Calderon.MixedKernelConstruction.MixedKernelCurrentCommonPair
import Calderon.MixedKernelConstruction.MixedKernelProductOpenUCP
import Calderon.MixedKernelConstruction.MixedKernelCenteredRooms
import Calderon.MixedKernelConstruction.MixedKernelFiniteInterpolation
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNearOne
import Calderon.MixedKernelConstruction.MixedKernelAnnulusGeometry
import Calderon.MixedKernelConstruction.MixedKernelKnownSideCompactBuffer
import Calderon.MixedKernelConstruction.MixedKernelActualSeparatorAnchors
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNeighborhood
import Calderon.MixedKernelConstruction.MixedKernelCompatibleGluing
import Calderon.MixedKernelConstruction.MixedKernelFullCrossAssembly
import Calderon.MixedKernelConstruction.MixedKernelCurrentSeriesConstruction
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise

/-- The restricted and full-domain representatives are the SAME function on the smaller open set. -/
theorem restrictRep_eq_harmonicRep (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (hpos : ∀ x ∈ D, (A x).PosDef) (O : Set R3) (hO : IsOpen O) (hOD : O ⊆ D)
    (u : harmonicSub D hD A hA) :
    EqOn (restrictRep D hD A hA hpos O hO hOD u) (harmonicRep D hD A hA hpos u) O := by
  have hOrep := (restrictRep_spec_and_jet_bound D hD A hA hpos O hO hOD).1 u
  have hDrep := harmonicRep_spec D hD A hA hpos u
  apply eqOn_of_ae_eq_restrict_open hO hOrep.1.continuousOn (hDrep.1.mono hOD).continuousOn
  exact hOrep.2.1.trans ((harmonicRestrict_ae D hD A hA O hOD u).trans
    (ae_restrict_of_ae_restrict_of_subset hOD hDrep.2.1.symm))

/-- The genuine D-harmonic Hilbert expansion converges pointwise after restriction to O. -/
theorem harmonicBasis_restrict_hasSum_pointwise (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (hpos : ∀ x ∈ D, (A x).PosDef) (O : Set R3) (hO : IsOpen O) (hOD : O ⊆ D)
    {ι : Type*} (w : HilbertBasis ι ℝ (harmonicSub D hD A hA))
    (v : harmonicSub D hD A hA) (x : R3) (hx : x ∈ O) :
    HasSum (fun i => restrictRep D hD A hA hpos O hO hOD (w i) x * w.repr v i)
      (restrictRep D hD A hA hpos O hO hOD v x) := by
  obtain ⟨Ev, hev⟩ : ∃ Ev : harmonicSub D hD A hA →L[ℝ] ℝ,
      ∀ u : harmonicSub D hD A hA, Ev u = harmonicRep D hD A hA hpos u x := by
    refine ⟨(ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => R3) ℝ 0).comp
        (harmonicJetCLM D hD A hA hpos 0 x (hOD hx)), fun u => ?_⟩
    exact iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := harmonicRep D hD A hA hpos u) (x := x) 0
  have hs : HasSum (fun i => Ev (w.repr v i • w i)) (Ev v) := (w.hasSum_repr v).mapL Ev
  have hEq : ∀ u : harmonicSub D hD A hA, restrictRep D hD A hA hpos O hO hOD u x = Ev u :=
    fun u => (restrictRep_eq_harmonicRep D hD A hA hpos O hO hOD u hx).trans (hev u).symm
  have hterm : ∀ i, restrictRep D hD A hA hpos O hO hOD (w i) x * w.repr v i =
      Ev (w.repr v i • w i) := fun i =>
    (congrArg (fun t => t * w.repr v i) (hEq (w i))).trans
      ((mul_comm _ _).trans ((map_smul Ev (w.repr v i) (w i)).trans (smul_eq_mul _ _)).symm)
  exact (congrArg₂ (fun (f : ι → ℝ) (a : ℝ) => HasSum f a) (funext hterm) (hEq v)).mpr hs

/-- Full-domain basis restriction identifies the SAME continuous data with its scalar series. -/
theorem harmonicBasis_restrict_series_eq (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (hpos : ∀ x ∈ D, (A x).PosDef) (O : Set R3) (hO : IsOpen O) (hOD : O ⊆ D)
    {ι : Type*} (w : HilbertBasis ι ℝ (harmonicSub D hD A hA))
    (v : harmonicSub D hD A hA) (f : R3 → ℝ) (hfc : ContinuousOn f O)
    (hf : (harmonicRestrict D hD A hA O hOD v : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict O] f) :
    EqOn f (fun x => ∑' i, restrictRep D hD A hA hpos O hO hOD (w i) x * w.repr v i) O := by
  have hrep := (restrictRep_spec_and_jet_bound D hD A hA hpos O hO hOD).1 v
  have heq : EqOn f (restrictRep D hD A hA hpos O hO hOD v) O :=
    eqOn_of_ae_eq_restrict_open hO hfc hrep.1.continuousOn (hf.symm.trans hrep.2.1.symm)
  intro x hx
  exact (heq hx).trans (harmonicBasis_restrict_hasSum_pointwise D hD A hA hpos O hO hOD w v x hx).tsum_eq.symm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
