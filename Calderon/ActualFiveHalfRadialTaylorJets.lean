import Calderon.ActualReferenceAdjointFiveHalfRadialFamily
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.ActualReferenceRadialEndpointOpenLocus
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Five" => SphereSobolev (5/2:ℝ)
local notation "Hi" => SphereSobolev (3/2:ℝ)
attribute [local irreducible] referenceAdjointFiveHalfRadialFamily secondTaylorRemainder
  referenceRadialEndpointInvertibleLocus

private lemma compact_jet_cap
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → V) (K : Set E) (hK : IsCompact K)
    (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) (N : ℕ) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ n : ℕ, n ≤ N → ∀ z ∈ K,
      ‖iteratedFDeriv ℝ n f z‖ ≤ C0 := by
  classical
  have hb (n : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ z ∈ K,
      ‖iteratedFDeriv ℝ n f z‖ ≤ c := by
    have hc : ContinuousOn (iteratedFDeriv ℝ n f) K :=
      fun z hz => ((hf z hz).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
    obtain ⟨c,hc⟩ := hK.exists_bound_of_continuousOn hc
    exact ⟨max c 0,le_max_right _ _,fun z hz => (hc z hz).trans (le_max_left _ _)⟩
  choose c hc hcBound using hb
  have hSum : 0 ≤ ∑ i : Fin (N+1), c i.val := Finset.sum_nonneg (fun i _ => hc i.val)
  refine ⟨(∑ i : Fin (N+1),c i.val)+1,by linarith,?_⟩
  intro n hn z hz
  let i : Fin (N+1) := ⟨n,Nat.lt_succ_of_le hn⟩
  exact (hcBound n z hz).trans
    ((Finset.single_le_sum (fun j _ => hc j.val) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right zero_le_one))

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceFiveHalfAdjointRadialSecondRemainder (z : Pphys) : Five →L[ℝ] Hi :=
  secondTaylorRemainder (fun t : ℝ => referenceAdjointFiveHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2

theorem contDiffAt_referenceFiveHalfAdjointRadialSecondRemainder_of_segment
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ theta ∈ Icc (0:ℝ) 1, (q,(y,theta*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (referenceFiveHalfAdjointRadialSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (q,(y,r)) := by
  let F : (ℝ × R3) × ℝ → Five →L[ℝ] Hi := fun z => referenceAdjointFiveHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1.1,(z.1.2,z.2))
  let Ω : Set ((ℝ × R3) × ℝ) := {z | (z.1.1,(z.1.2,z.2)) ∈
    referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0}
  have hOpen := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hΩ : IsOpen Ω := hOpen.preimage
    (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hFive := contDiffOn_referenceAdjointFiveHalfRadialFamily_invertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hSmooth : ContDiffOn ℝ ∞ F Ω := by
    intro z hz
    exact ((hFive.contDiffAt (hOpen.mem_nhds hz)).comp z
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hT := contDiffAt_secondTaylorRemainder_joint_of_open_segment F Ω hΩ hSmooth (q,y) r hSegment
  have hReorder : ContDiff ℝ ∞ (fun z : Pphys => ((z.1,z.2.1),z.2.2)) := by fun_prop
  unfold referenceFiveHalfAdjointRadialSecondRemainder
  exact hT.comp (f := fun z : Pphys => ((z.1,z.2.1),z.2.2)) (q,(y,r)) hReorder.contDiffAt


theorem exists_uniform_referenceFiveHalfAdjointRadialSecondRemainder_joint_jets
    (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ ∀ N : ℕ,
      let K : Set Pphys := Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)
      (∀ z ∈ K, ContDiffAt ℝ ∞ (referenceFiveHalfAdjointRadialSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) z) ∧
      ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ n : ℕ, n ≤ N → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ n (referenceFiveHalfAdjointRadialSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) z‖ ≤ C0 := by
  obtain ⟨d0,hd0,hd0ρ,hRoom⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let d := min d0 1
  refine ⟨d,lt_min hd0 one_pos,(min_le_left _ _).trans hd0ρ,min_le_right _ _,?_⟩
  intro N K
  have hSmooth (z : Pphys) (hz : z ∈ K) : ContDiffAt ℝ ∞
      (referenceFiveHalfAdjointRadialSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) z := by
    apply contDiffAt_referenceFiveHalfAdjointRadialSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
    intro theta htheta
    have hr : |z.2.2| ≤ d0 := (abs_le.mpr hz.2.2).trans (min_le_left _ _)
    have htr : |theta*z.2.2| ≤ d0 := by
      rw [abs_mul,abs_of_nonneg htheta.1]
      calc theta*|z.2.2| ≤ 1*|z.2.2| := mul_le_mul_of_nonneg_right htheta.2 (abs_nonneg _)
           _ ≤ d0 := by simpa only [one_mul] using hr
    exact hRoom ⟨hz.1,hz.2.1,abs_le.mp htr⟩
  exact ⟨hSmooth,compact_jet_cap _ K (isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)) hSmooth N⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
