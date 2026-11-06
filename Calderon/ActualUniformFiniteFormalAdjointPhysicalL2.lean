import Calderon.ActualFiniteFormalAdjointPhysicalL2

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)


attribute [local irreducible] referenceFiniteHalfFormalAdjointPhysicalSection
  referenceFormalAdjointPhysicalDensityOperator
  referenceHighFullAdjointFirstAction
  referenceLowerFullAdjointFirstAction
  referenceFiniteHighFullAdjointFirstSection
  sphereSobolevInclusionL
  sphereSobolevPartialSumL
  referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint
  referenceMetricGramFrame
  referenceFrameConnectionCoefficient
  referenceStrongDriftFamily
  sphereSobolevZeroEquiv

lemma exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_graph_uniform_metric
    (hreg : FixedDirichletRegularity) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ ρ ∧
      ∀ (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2),
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d0 ∧ R y ≠ 0) → ∀ y : R3,
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (referenceFiniteHalfFormalAdjointPhysicalSection
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u y) =
        referenceFormalAdjointPhysicalDensityOperator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
          (fun x => sphereSobolevPartialSumL (3/2 : ℝ) n (u x)) y := by
  obtain ⟨d0,hd0,hdρ,hGraph⟩ := exists_reference_commonRadius_fullAdjointSecondSection_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  refine ⟨d0,hd0,hdρ,?_⟩
  intro g2 hg2 n q hq R hR u hu hCompact hSupportRoom y
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Pn := sphereSobolevPartialSumL (3/2 : ℝ) n
  have hInput (c : R3 → ℝ) :
      (fun x => Pn (c x • u x)) = (fun x => c x • Pn (u x)) := by
    funext x
    exact Pn.map_smul (c x) (u x)
  have hOrdered (i j : Fin 3) :
      J (referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => referenceFiniteHighFullAdjointFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R
          (fun x => (R x * referenceDensityPrincipalFrameCoefficient g g2 L q x i j) • u x) z i) y j) =
      referenceLowerFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => referenceHighFullAdjointFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
          (fun x => (R x * referenceDensityPrincipalFrameCoefficient g g2 L q x i j) • Pn (u x)) z i) y j := by
    let c : R3 → ℝ := fun x => R x * referenceDensityPrincipalFrameCoefficient g g2 L q x i j
    let U : R3 → SphereSobolev (3/2 : ℝ) := fun x => c x • u x
    have hQ : ContDiff ℝ ∞ (fun x => referenceDensityPrincipalFrameCoefficient g g2 L q x i j) :=
      (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
        (contDiff_const.prodMk contDiff_id)
    have hU : ContDiff ℝ ∞ U := (hR.mul hQ).smul hu
    have hUSupport : tsupport U ⊆ tsupport u := by
      apply closure_minimal ?_ (isClosed_tsupport u)
      intro x hx
      by_contra hxu
      have hZero : u x = 0 := image_eq_zero_of_notMem_tsupport hxu
      change U x ≠ 0 at hx
      exact hx (by simp only [U,hZero,smul_zero])
    have hSupportU : ∀ x ∈ tsupport U, ‖x-y0‖ < ρ ∧ |R x| < d0 ∧ R x ≠ 0 :=
      fun x hx => hSupportRoom x (hUSupport hx)
    have hG := hGraph n q hq R hR U hU hSupportU i j y
    have hTransport := congrArg
      (fun V : R3 → SphereSobolev (3/2 : ℝ) => referenceLowerFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => referenceHighFullAdjointFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R V z i) y j) (hInput c)
    exact hG.trans hTransport
  change J (referenceFiniteHalfFormalAdjointPhysicalSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u y) = _
  simp only [referenceFiniteHalfFormalAdjointPhysicalSection,
    referenceFormalAdjointPhysicalDensityOperator,map_add,map_sub,map_sum]
  apply congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
  · apply congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z)
    · apply Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      intro i hi
      apply Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      intro j hj
      exact hOrdered i j
    · apply Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      intro k hk
      exact congrArg
        (fun V : R3 → SphereSobolev (3/2 : ℝ) => J (referenceHighFullAdjointFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R V y k))
        (hInput (fun x => R x * ∑ i : Fin 3, ∑ j : Fin 3,
          referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
            referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j))
  · apply Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    intro i hi
    exact congrArg
      (fun V : R3 → SphereSobolev (3/2 : ℝ) => J (referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R V y i))
      (hInput (fun x => R x * normalizedSecondDriftFrameJoint g g2 L i (q,x)))

lemma exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_global_uniform_metric
    (hreg : FixedDirichletRegularity) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ ρ ∧
      ∀ (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2),
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d0 ∧ R y ≠ 0) →
        ContDiff ℝ ∞ (fun y => referenceFiniteHalfFormalAdjointPhysicalSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u y) ∧
        HasCompactSupport (fun y => referenceFiniteHalfFormalAdjointPhysicalSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u y) := by
  classical
  obtain ⟨dS,hdS,hdSρ,hSecond⟩ := exists_reference_commonRadius_fullAdjointSecondSection_global
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨lam,Lam,d,hlam,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨min dS (d/2),lt_min hdS (show 0 < d/2 by positivity),
    (min_le_left _ _).trans hdSρ,?_⟩
  intro g2 hg2 n q hq R hR u hu hCompact hSupportRoom
  let Pn := sphereSobolevPartialSumL (3/2 : ℝ) n
  have hScalarSupport (c : R3 → ℝ) : tsupport (fun x => c x • u x) ⊆ tsupport u :=
    tsupport_smul_subset_right c u
  have hFirst (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (k : Fin 3) :
      ContDiff ℝ ∞ (fun y => referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun x => Pn (c x • u x)) y k) ∧
      HasCompactSupport (fun y => referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun x => Pn (c x • u x)) y k) := by
    let f : R3 → SphereSobolev (3/2 : ℝ) := fun x => Pn (c x • u x)
    let Y : R3 → SphereSobolev (1/2 : ℝ) := fun y => referenceHighFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R f y k
    have hf : ContDiff ℝ ∞ f := Pn.contDiff.comp (hc.smul hu)
    have hfSupport : tsupport f ⊆ tsupport u :=
      (tsupport_comp_subset (map_zero Pn) (fun x => c x • u x)).trans (hScalarSupport c)
    have hYSupport : tsupport Y ⊆ tsupport u :=
      (tsupport_referenceHighFullAdjointFirstAction_subset
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R f k).trans hfSupport
    have hSmooth : ContDiff ℝ ∞ Y := by
      apply contDiff_iff_contDiffAt.mpr
      intro y
      by_cases hy : y ∈ tsupport u
      · have hs := hSupportRoom y hy
        have hrHalf : |R y| < d/2 := hs.2.1.trans_le (min_le_right _ _)
        have hrD : |R y| ≤ d := by linarith only [hrHalf,hd]
        have hp : (q,(y,R y)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) := by
          refine ⟨hq,?_,abs_le.mp hrD⟩
          simpa only [mem_closedBall,dist_eq_norm] using hs.1.le
        have ha := hRoom (q,(y,R y)) hp
        exact contDiffAt_referenceHighFullAdjointFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R f y k
            hf.contDiffAt hR.contDiffAt hs.2.2 ha.2.2.2.2 ha.2.2.2.1.2
      · have hZero : Y =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) :=
          notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hYSupport h))
        exact (contDiffAt_const : ContDiffAt ℝ ∞
          (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) y).congr_of_eventuallyEq hZero
    exact ⟨hSmooth,hCompact.of_isClosed_subset (isClosed_tsupport Y) hYSupport⟩
  let alpha : Fin 3 → Fin 3 → R3 → ℝ := fun i j x =>
    R x * referenceDensityPrincipalFrameCoefficient g g2 L q x i j
  let gamma : Fin 3 → R3 → ℝ := fun k x => R x * ∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
      referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j
  let drift : Fin 3 → R3 → ℝ := fun i x =>
    R x * normalizedSecondDriftFrameJoint g g2 L i (q,x)
  have hQ (i j : Fin 3) :
      ContDiff ℝ ∞ (fun x => referenceDensityPrincipalFrameCoefficient g g2 L q x i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
      (contDiff_const.prodMk contDiff_id)
  have hGamma (i j k : Fin 3) : ContDiff ℝ ∞ (fun x =>
      referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j) :=
    AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field g hg L q
      (fun x => referenceMetricGramFrame g L (q,x) i)
      (contDiff_referenceMetricGramFrame_slice g hg L q i) k j
  have hAlpha (i j : Fin 3) : ContDiff ℝ ∞ (alpha i j) := hR.mul (hQ i j)
  have hGammaScalar (k : Fin 3) : ContDiff ℝ ∞ (gamma k) :=
    hR.mul (ContDiff.sum (fun i hi => ContDiff.sum (fun j hj => (hQ i j).mul (hGamma i j k))))
  have hDrift (i : Fin 3) : ContDiff ℝ ∞ (drift i) :=
    hR.mul ((contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp
      (contDiff_const.prodMk contDiff_id))
  let A : Fin 3 → Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun i j y =>
    referenceHighFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun z => referenceFiniteHighFullAdjointFirstSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R
        (fun x => alpha i j x • u x) z i) y j
  let Cseq : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k y =>
    referenceHighFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun x => Pn (gamma k x • u x)) y k
  let Dseq : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun i y =>
    referenceHighFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun x => Pn (drift i x • u x)) y i
  have hA (i j : Fin 3) : ContDiff ℝ ∞ (A i j) ∧ HasCompactSupport (A i j) := by
    have hU : ContDiff ℝ ∞ (fun x => alpha i j x • u x) := (hAlpha i j).smul hu
    have hUc : HasCompactSupport (fun x => alpha i j x • u x) :=
      hCompact.of_isClosed_subset (isClosed_tsupport _) (hScalarSupport (alpha i j))
    have hRoomU : ∀ x ∈ tsupport (fun z => alpha i j z • u z),
        ‖x-y0‖ < ρ ∧ |R x| < dS ∧ R x ≠ 0 := by
      intro x hx
      have hs := hSupportRoom x (hScalarSupport (alpha i j) hx)
      exact ⟨hs.1,hs.2.1.trans_le (min_le_left _ _),hs.2.2⟩
    exact hSecond n q hq R hR (fun x => alpha i j x • u x) hU hUc hRoomU i j
  have hC (k : Fin 3) : ContDiff ℝ ∞ (Cseq k) ∧ HasCompactSupport (Cseq k) :=
    hFirst (gamma k) (hGammaScalar k) k
  have hDseq (i : Fin 3) : ContDiff ℝ ∞ (Dseq i) ∧ HasCompactSupport (Dseq i) :=
    hFirst (drift i) (hDrift i) i
  have hASmooth : ContDiff ℝ ∞ (fun y => ∑ i : Fin 3, ∑ j : Fin 3, A i j y) :=
    ContDiff.sum (fun i hi => ContDiff.sum (fun j hj => (hA i j).1))
  have hCSmooth : ContDiff ℝ ∞ (fun y => ∑ k : Fin 3, Cseq k y) :=
    ContDiff.sum (fun k hk => (hC k).1)
  have hDSmooth : ContDiff ℝ ∞ (fun y => ∑ i : Fin 3, Dseq i y) :=
    ContDiff.sum (fun i hi => (hDseq i).1)
  have hACompact : HasCompactSupport (fun y => ∑ i : Fin 3, ∑ j : Fin 3, A i j y) := by
    have hInner (i : Fin 3) : HasCompactSupport (∑ j : Fin 3, A i j) :=
      HasCompactSupport.finset_sum (fun j hj => (hA i j).2)
    have hOuter : HasCompactSupport (∑ i : Fin 3, ∑ j : Fin 3, A i j) :=
      HasCompactSupport.finset_sum (fun i hi => hInner i)
    have hEq : (∑ i : Fin 3, ∑ j : Fin 3, A i j) =
        (fun y => ∑ i : Fin 3, ∑ j : Fin 3, A i j y) := by
      funext y
      simp only [Finset.sum_apply]
    exact (congrArg (fun f : R3 → SphereSobolev (1/2 : ℝ) => HasCompactSupport f) hEq).mp hOuter
  have hCCompact : HasCompactSupport (fun y => ∑ k : Fin 3, Cseq k y) := by
    have h : HasCompactSupport (∑ k : Fin 3, Cseq k) :=
      HasCompactSupport.finset_sum (fun k hk => (hC k).2)
    have hEq : (∑ k : Fin 3, Cseq k) = (fun y => ∑ k : Fin 3, Cseq k y) := by
      funext y
      simp only [Finset.sum_apply]
    exact (congrArg (fun f : R3 → SphereSobolev (1/2 : ℝ) => HasCompactSupport f) hEq).mp h
  have hDCompact : HasCompactSupport (fun y => ∑ i : Fin 3, Dseq i y) := by
    have h : HasCompactSupport (∑ i : Fin 3, Dseq i) :=
      HasCompactSupport.finset_sum (fun i hi => (hDseq i).2)
    have hEq : (∑ i : Fin 3, Dseq i) = (fun y => ∑ i : Fin 3, Dseq i y) := by
      funext y
      simp only [Finset.sum_apply]
    exact (congrArg (fun f : R3 → SphereSobolev (1/2 : ℝ) => HasCompactSupport f) hEq).mp h
  have hSmooth := (hASmooth.sub hCSmooth).add hDSmooth
  have hCompactTotal : HasCompactSupport (fun y =>
      (∑ i : Fin 3, ∑ j : Fin 3, A i j y) - (∑ k : Fin 3, Cseq k y) +
        ∑ i : Fin 3, Dseq i y) := by
    have hAZ : (fun y => ∑ i : Fin 3, ∑ j : Fin 3, A i j y) =ᶠ[coclosedCompact R3]
        (0 : R3 → SphereSobolev (1/2 : ℝ)) := hasCompactSupport_iff_eventuallyEq.mp hACompact
    have hCZ : (fun y => ∑ k : Fin 3, Cseq k y) =ᶠ[coclosedCompact R3]
        (0 : R3 → SphereSobolev (1/2 : ℝ)) := hasCompactSupport_iff_eventuallyEq.mp hCCompact
    have hDZ : (fun y => ∑ i : Fin 3, Dseq i y) =ᶠ[coclosedCompact R3]
        (0 : R3 → SphereSobolev (1/2 : ℝ)) := hasCompactSupport_iff_eventuallyEq.mp hDCompact
    apply hasCompactSupport_iff_eventuallyEq.mpr
    filter_upwards [hAZ,hCZ,hDZ] with y hA0 hC0 hD0
    change (∑ i : Fin 3, ∑ j : Fin 3, A i j y) - (∑ k : Fin 3, Cseq k y) +
      (∑ i : Fin 3, Dseq i y) = 0
    have hSub := congrArg₂ (fun a b : SphereSobolev (1/2 : ℝ) => a-b) hA0 hC0
    have hSum := congrArg₂ (fun a b : SphereSobolev (1/2 : ℝ) => a+b) hSub hD0
    exact hSum.trans (by simp only [Pi.zero_apply,sub_self,add_zero])
  constructor
  · simpa only [referenceFiniteHalfFormalAdjointPhysicalSection,A,Cseq,Dseq,
      alpha,gamma,drift,Pn,Pi.add_apply,Pi.sub_apply] using hSmooth
  · simpa only [referenceFiniteHalfFormalAdjointPhysicalSection,A,Cseq,Dseq,
      alpha,gamma,drift,Pn,Pi.add_apply,Pi.sub_apply] using hCompactTotal

lemma exists_reference_commonRadius_finiteFormalAdjointPhysical_L2_uniform_metric
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2),
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < δ ∧ R y ≠ 0) →
      ∃ f : R3 → SphereL2, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        MemLp f 2 (volume : Measure R3) ∧ ∀ y : R3,
          sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
            (sphereSobolevZeroEquiv hO hD (f y)) =
          referenceFormalAdjointPhysicalDensityOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
            (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (u z)) y := by
  obtain ⟨dG,hdG,hdGρ,hGraph⟩ := exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_graph_uniform_metric
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨dS,hdS,hdSρ,hGlobal⟩ := exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_global_uniform_metric
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  refine ⟨min dG dS,lt_min hdG hdS,(min_le_left _ _).trans hdGρ,?_⟩
  intro g2 hg2 n q hq R hR u hu hCompact hSupportRoom
  have hSupportG : ∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < dG ∧ R y ≠ 0 := by
    intro y hy
    have hs := hSupportRoom y hy
    exact ⟨hs.1,hs.2.1.trans_le (min_le_left _ _),hs.2.2⟩
  have hSupportS : ∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < dS ∧ R y ≠ 0 := by
    intro y hy
    have hs := hSupportRoom y hy
    exact ⟨hs.1,hs.2.1.trans_le (min_le_right _ _),hs.2.2⟩
  let W : R3 → SphereSobolev (1/2 : ℝ) := fun y => referenceFiniteHalfFormalAdjointPhysicalSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u y
  have hWG := hGraph g2 hg2 n q hq R hR u hu hCompact hSupportG
  have hWS : ContDiff ℝ ∞ W ∧ HasCompactSupport W :=
    hGlobal g2 hg2 n q hq R hR u hu hCompact hSupportS
  let Z := sphereSobolevZeroEquiv hO hD
  let I0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let T0 : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereL2 :=
    Z.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp I0
  let f : R3 → SphereL2 := fun y => Z.symm (I0 (W y))
  have hfSmooth : ContDiff ℝ ∞ f := T0.contDiff.comp hWS.1
  have hfSupport : tsupport f ⊆ tsupport W := tsupport_comp_subset (map_zero T0) W
  have hfCompact : HasCompactSupport f :=
    hWS.2.of_isClosed_subset (isClosed_tsupport f) hfSupport
  have hfMem : MemLp f 2 (volume : Measure R3) :=
    hfSmooth.continuous.memLp_of_hasCompactSupport hfCompact
  refine ⟨f,hfSmooth,hfCompact,hfMem,?_⟩
  intro y
  have hCancel := congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num))
    (Z.apply_symm_apply (I0 (W y)))
  have hTrans := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (W y))
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  exact hCancel.trans (hTrans.trans (hWG y))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_graph_uniform_metric
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_global_uniform_metric
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finiteFormalAdjointPhysical_L2_uniform_metric
