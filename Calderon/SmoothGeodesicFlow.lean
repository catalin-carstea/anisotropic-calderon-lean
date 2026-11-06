import Calderon.GeodesicFlow
import TauCeti.Analysis.ODE.InitialCondition
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology NNReal
namespace OAI.AnisotropicCalderon.ConnectionError

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem contDiff_infty_globalSolution (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun p : E × ℝ => ODE.globalSolution v hv p.1 p.2) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n _
  exact (ODE.contDiff_globalSolution n v hv (hvs.of_le (by simp))).of_le
    (by exact_mod_cast Nat.le_succ n)

theorem globalSolution_stationary (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (a : E) (ha : v a = 0) (t : ℝ) :
    ODE.globalSolution v hv a t = a := by
  have hc : (fun _ : ℝ => a) = ODE.globalSolution v hv a := by
    apply ODE.eq_globalSolution
    intro s
    simpa only [ha] using
      (show HasDerivAt (fun _ : ℝ => a) 0 s from hasDerivAt_const _ _)
  exact (congrFun hc t).symm

end Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem geodesicPhaseField_zero_velocity (Q M : E → E →L[ℝ] E) (y : E) :
    geodesicPhaseField Q M (y,0) = 0 := by
  simp [geodesicPhaseField]

variable [FiniteDimensional ℝ E]

theorem exists_smooth_geodesic_flow_on_unit_interval (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (y0 : E) :
    ∃ (Φ : (E × E) → ℝ → E × E) (A : Set (E × E)),
      IsOpen A ∧ (y0,0) ∈ A ∧
      ContDiff ℝ ∞ (fun p : (E × E) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧
      (∀ t, Φ (y0,0) t = (y0,0)) ∧
      (∀ z t u, Φ z (t + u) = Φ (Φ z t) u) ∧
      ∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (Φ z) (geodesicPhaseField Q M (Φ z t)) t := by
  let a : E × E := (y0,0)
  have hs : ContDiffOn ℝ (∞ + 1) (geodesicPhaseField Q M) univ := by
    simpa using (contDiff_geodesicPhaseField Q M hQ hM).contDiffOn
  obtain ⟨v,K,hvs,hv,heq⟩ :=
    hs.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional
      (x := a) (by simp)
  have hvs' : ContDiff ℝ ∞ v := by simpa using hvs
  have hz : v a = 0 := by
    rw [heq.self_of_nhds]
    exact geodesicPhaseField_zero_velocity Q M y0
  have hstat : ∀ t, ODE.globalSolution v hv a t = a :=
    globalSolution_stationary v hv a hz
  have hc := (contDiff_infty_globalSolution v hv hvs').continuous
  obtain ⟨U,hUeq,hU,haU⟩ := mem_nhds_iff.mp heq
  have hopen : IsOpen ((fun p : (E × E) × ℝ =>
      ODE.globalSolution v hv p.1 p.2) ⁻¹' U) := hU.preimage hc
  have hsub : ({a} : Set (E × E)) ×ˢ Icc (0 : ℝ) 1 ⊆
      (fun p : (E × E) × ℝ => ODE.globalSolution v hv p.1 p.2) ⁻¹' U := by
    intro p hp
    change ODE.globalSolution v hv p.1 p.2 ∈ U
    rw [show p.1 = a from hp.1,hstat]
    exact haU
  obtain ⟨A,T,hA,_,haA,hIT,hAT⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hopen hsub
  refine ⟨ODE.globalSolution v hv,A,hA,haA (mem_singleton a),
    contDiff_infty_globalSolution v hv hvs',
    ODE.globalSolution_zero v hv,hstat,ODE.globalSolution_add v hv,?_⟩
  intro z hzA t ht
  have hpos : ODE.globalSolution v hv z t ∈ U := hAT (a := (z,t)) ⟨hzA,hIT ht⟩
  rw [← hUeq hpos]
  exact ODE.hasDerivAt_globalSolution v hv z t

end OAI.AnisotropicCalderon.ConnectionError
