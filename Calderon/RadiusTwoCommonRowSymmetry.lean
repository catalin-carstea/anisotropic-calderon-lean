import Calderon.RadiusTwoCommonRowFixedCutoffPairingLimit
import Calderon.RadiusTwoOffPoleNestedCutoffRoom
import Calderon.RadiusTwoCommonDeltaLocalL2Pairing
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Distributions Gradient InnerProductSpace Topology ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
variable (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1) (r : R3) (hr : r ∈ ball (0 : R3) b)
    (L : RadiusTwoL2)
    (hLimitL : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence b hb hb1 r hr n,
          (radiusTwoCommonNormalizedDeltaSequence b hb hb1 r hr n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 L))
include hreg hcalc hg ha ha1 hq hLimit hb hb1 hr hLimitL


theorem radiusTwoCommonRow_symmetry_of_continuous_representatives
    (F G : R3 → ℝ)
    (hF : ContinuousOn F ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}))
    (hG : ContinuousOn G ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • r}))
    (hKF : (K : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] F)
    (hLG : (L : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] G)
    (hNe : (2 : ℝ) • r ≠ (2 : ℝ) • q) :
    F ((2 : ℝ) • r) = G ((2 : ℝ) • q) := by
  have hrRoom : (2 : ℝ) • r ∈ ball (0 : R3) (2*b) := by
    rw [mem_ball_zero_iff,norm_smul]
    norm_num
    exact mem_ball_zero_iff.mp hr
  have hqRoom : (2 : ℝ) • q ∈ ball (0 : R3) (2*a) := by
    rw [mem_ball_zero_iff,norm_smul]
    norm_num
    exact mem_ball_zero_iff.mp hq
  have hrN : (2 : ℝ) • r ∈ (radiusTwoOpens : Set R3) :=
    ball_subset_ball (by linarith : 2*b ≤ 2) hrRoom
  have hqN : (2 : ℝ) • q ∈ (radiusTwoOpens : Set R3) :=
    ball_subset_ball (by linarith : 2*a ≤ 2) hqRoom
  have hrOff : (2 : ℝ) • r ∈ (radiusTwoOpens : Set R3) \ {(2 : ℝ) • q} :=
    ⟨hrN,by simpa only [mem_singleton_iff] using hNe⟩
  obtain ⟨ε,hε,η,χ,hηOne,hχOne,hχRoom,hηχ,hBallRoom,V,hV,hηV,hχV⟩ :=
    exists_radiusTwo_offpole_nested_cutoff_room ((2 : ℝ) • q) ((2 : ℝ) • r) hrOff
  have hpχ : (2 : ℝ) • q ∉ tsupport (χ : R3 → ℝ) := by
    intro hp
    exact (hχRoom hp).2 (by simp)
  have hpη : (2 : ℝ) • q ∉ tsupport (η : R3 → ℝ) := fun hp => hpχ (hηχ hp)
  obtain ⟨Mχ,hMχ,hAbsχ,hGradχ⟩ :=
    (χ.contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le χ.hasCompactSupport
  obtain ⟨Mη,hMη,hAbsη,hGradη⟩ :=
    (η.contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le η.hasCompactSupport
  have hVan : ∃ δ : ℝ, 0 < δ ∧ ∀ z : R3,
      dist ((1/2 : ℝ) • z) q < δ → χ z = 0 := by
    have hZero : (χ : R3 → ℝ) =ᶠ[𝓝 ((2 : ℝ) • q)] (0 : R3 → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hpχ
    have hComp := hZero.comp_tendsto ((continuous_const_smul (2 : ℝ)).tendsto q)
    have hNear : ∀ᶠ y in 𝓝 q, χ ((2 : ℝ) • y) = 0 := by
      filter_upwards [hComp] with y hy
      exact hy
    obtain ⟨δ,hδ,hδZero⟩ := Metric.mem_nhds_iff.mp hNear
    refine ⟨δ,hδ,?_⟩
    intro z hz
    have h := hδZero (show (1/2 : ℝ) • z ∈ ball q δ from hz)
    have hCancel : (2 : ℝ) • ((1/2 : ℝ) • z) = z := by
      rw [smul_smul]
      norm_num
    change χ ((2 : ℝ) • ((1/2 : ℝ) • z)) = 0 at h
    rw [hCancel] at h
    exact h
  let W : Set R3 := ball ((2 : ℝ) • r) ε ∩ ball (0 : R3) (2*b)
  have hW : IsOpen W := isOpen_ball.inter isOpen_ball
  have hrW : (2 : ℝ) • r ∈ W := ⟨mem_ball_self hε,hrRoom⟩
  have hWR : W ⊆ ball (0 : R3) (2*b) := inter_subset_right
  have hWOff : W ⊆ (radiusTwoOpens : Set R3) \ {(2 : ℝ) • q} :=
    fun z hz => hBallRoom hz.1
  have hηW : ∀ z ∈ W, η z = 1 := fun z hz => hηOne z hz.1
  have hχW : ∀ z ∈ W, χ z = 1 := by
    intro z hz
    apply hχOne z
    apply subset_tsupport (η : R3 → ℝ)
    change η z ≠ 0
    rw [hηW z hz]
    exact one_ne_zero
  have hFilter : ae ((volume : Measure R3).restrict W) ≤
      ae ((volume : Measure R3).restrict radiusTwoOpens) :=
    ae_mono (Measure.restrict_mono_set volume (fun z hz => (hWOff hz).1))
  have hFirst := radiusTwoCommonRow_fixed_cutoff_pairing_tendsto
    hreg hcalc g hg a ha ha1 q hq K hLimit b hb hb1 r hr L hLimitL
    η χ V hV hηV hχV hχOne hpη Mη Mχ hMη hMχ hAbsη hGradη hAbsχ hGradχ hVan
    W hW hrW hWR hηW hχW F (hF.mono hWOff) (hKF.filter_mono hFilter)
  have hOpen : IsOpen ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • r}) := by
    exact IsOpen.sdiff isOpen_ball isClosed_singleton
  have hqOff : (2 : ℝ) • q ∈ (radiusTwoOpens : Set R3) \ {(2 : ℝ) • r} :=
    ⟨hqN,by simpa only [mem_singleton_iff] using hNe.symm⟩
  have hSecond := radiusTwoCommonDelta_local_L2_pairing_tendsto a ha ha1 q hq L
    ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • r}) hOpen hqOff G
    (hG.continuousAt (hOpen.mem_nhds hqOff))
    (hLG.mono (fun z hz _ => hz))
  exact tendsto_nhds_unique hFirst hSecond

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoCommonRow_symmetry_of_continuous_representatives
