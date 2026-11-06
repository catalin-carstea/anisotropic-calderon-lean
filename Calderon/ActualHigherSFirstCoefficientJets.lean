import Calderon.ActualHigherSZeroCoefficientBounds
import Calderon.ActualDensityPrincipalFrameSmoothness
import Mathlib.Analysis.Calculus.ContDiff.Bounds
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFirstCoefficientJets
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation

section LocalCalculus
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The unchanged library composition estimate, localized to genuine ambient germs. -/
lemma norm_iteratedFDeriv_comp_le_at_two (f : E → F) (g : F → G) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    (n : ℕ) (hn : n ≤ 2) (C D : ℝ)
    (hC : ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (n.factorial : ℝ)*C*D^n := by
  obtain ⟨t,ht,hxt,hgtRaw⟩ := hg.contDiffOn' (m := (2 : ℕ∞ω)) (by simp) (by simp)
  have hgt : ContDiffOn ℝ (2 : ℕ∞ω) g t := by simpa using hgtRaw
  obtain ⟨u,hu,hxu,hfuRaw⟩ := hf.contDiffOn' (m := (2 : ℕ∞ω)) (by simp) (by simp)
  have hfu : ContDiffOn ℝ (2 : ℕ∞ω) f u := by simpa using hfuRaw
  have hpre : f ⁻¹' t ∈ 𝓝 x := hf.continuousAt.preimage_mem_nhds (ht.mem_nhds hxt)
  obtain ⟨v,hv,hvopen,hxv⟩ := _root_.mem_nhds_iff.mp hpre
  let s := u ∩ v
  have hs : IsOpen s := hu.inter hvopen
  have hx : x ∈ s := ⟨hxu,hxv⟩
  have hfs : ContDiffOn ℝ (2 : ℕ∞ω) f s := hfu.mono inter_subset_left
  have hst : MapsTo f s t := fun y hy => hv hy.2
  have hcg (i : ℕ) : iteratedFDerivWithin ℝ i g t (f x) = iteratedFDeriv ℝ i g (f x) :=
    iteratedFDerivWithin_eq_iteratedFDeriv ht.uniqueDiffOn (hg.of_le (by simp)) hxt
  have hcf (i : ℕ) : iteratedFDerivWithin ℝ i f s x = iteratedFDeriv ℝ i f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hf.of_le (by simp)) hx
  have hcomp := hg.comp x hf
  have hccomp : iteratedFDerivWithin ℝ n (g ∘ f) s x = iteratedFDeriv ℝ n (g ∘ f) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hcomp.of_le (by simp)) hx
  have hN : (n : ℕ∞ω) ≤ (2 : ℕ∞ω) := by exact_mod_cast hn
  have h := norm_iteratedFDerivWithin_comp_le hgt hfs hN ht.uniqueDiffOn hs.uniqueDiffOn
    hst hx (fun i hi => by rw [hcg]; exact hC i hi)
    (fun i hi hin => by rw [hcf]; exact hD i hi hin)
  rwa [hccomp] at h

/-- Local Leibniz; no assertion of smoothness outside the stated germ. -/
lemma norm_iteratedFDeriv_smul_le_at_two (f : E → ℝ) (g : E → F) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*‖iteratedFDeriv ℝ i f x‖*
        ‖iteratedFDeriv ℝ (n-i) g x‖ := by
  obtain ⟨u,hu,hxu,hfuRaw⟩ := hf.contDiffOn' (m := (2 : ℕ∞ω)) (by simp) (by simp)
  have hfu : ContDiffOn ℝ (2 : ℕ∞ω) f u := by simpa using hfuRaw
  obtain ⟨v,hv,hxv,hgvRaw⟩ := hg.contDiffOn' (m := (2 : ℕ∞ω)) (by simp) (by simp)
  have hgv : ContDiffOn ℝ (2 : ℕ∞ω) g v := by simpa using hgvRaw
  let s := u ∩ v
  have hs : IsOpen s := hu.inter hv
  have hx : x ∈ s := ⟨hxu,hxv⟩
  have hcf (i : ℕ) : iteratedFDerivWithin ℝ i f s x = iteratedFDeriv ℝ i f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hf.of_le (by simp)) hx
  have hcg (i : ℕ) : iteratedFDerivWithin ℝ i g s x = iteratedFDeriv ℝ i g x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hg.of_le (by simp)) hx
  have hcprod : iteratedFDerivWithin ℝ n (fun y => f y • g y) s x =
      iteratedFDeriv ℝ n (fun y => f y • g y) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn ((hf.smul hg).of_le (by simp)) hx
  have hN : (n : ℕ∞ω) ≤ (2 : ℕ∞ω) := by exact_mod_cast hn
  have h : ‖iteratedFDerivWithin ℝ n (fun y => f y • g y) s x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*‖iteratedFDerivWithin ℝ i f s x‖*
        ‖iteratedFDerivWithin ℝ (n-i) g s x‖ :=
    norm_iteratedFDerivWithin_smul_le (hfu.mono inter_subset_left)
      (hgv.mono inter_subset_right) hs.uniqueDiffOn hx hN
  simpa only [hcprod,hcf,hcg] using h

lemma small_profile_composition_jets (f : E → F) (g : F → G) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    (M T beta : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) (hb : 1 ≤ beta)
    (hgcap : ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n g (f x)‖ ≤ M)
    (h1 : ‖iteratedFDeriv ℝ 1 f x‖ ≤ T)
    (h2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ T*beta) :
    ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      (2*M*(T+1)^2)*beta^n := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hT1 : 1 ≤ T+1 := by linarith
  intro n hn
  have hd (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i f x‖ ≤ ((T+1)*beta)^i := by
    have hi2 : i ≤ 2 := hin.trans hn
    interval_cases i
    · exact h1.trans (by have := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ T+1); nlinarith)
    · have hh : T*beta ≤ ((T+1)*beta)^2 := by
        have ht : T ≤ T+1 := by linarith
        have hd0 : 1 ≤ (T+1)*beta := by nlinarith [mul_nonneg (sub_nonneg.mpr hT1) (sub_nonneg.mpr hb)]
        have hd1 : T*beta ≤ (T+1)*beta := mul_le_mul_of_nonneg_right ht hb0
        nlinarith [sq_nonneg ((T+1)*beta)]
      exact h2.trans hh
  have h := norm_iteratedFDeriv_comp_le_at_two f g x hf hg n hn M ((T+1)*beta)
    (fun i hi => hgcap i (hi.trans hn)) hd
  have hp : (n.factorial : ℝ)*(T+1)^n ≤ 2*(T+1)^2 := by
    interval_cases n <;> norm_num at * <;> nlinarith [sq_nonneg (T+1)]
  calc
    _ ≤ (n.factorial : ℝ)*M*(((T+1)*beta)^n) := h
    _ = M*((n.factorial : ℝ)*(T+1)^n)*beta^n := by rw [mul_pow]; ring
    _ ≤ M*(2*(T+1)^2)*beta^n := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hM) (pow_nonneg hb0 n)
    _ = _ := by ring
end LocalCalculus

section ProductBudget
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma product_jets_two (f : E → ℝ) (g : E → F) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (A B beta : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 ≤ beta)
    (hfcap : ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n f x‖ ≤ A*beta^n)
    (hgcap : ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n g x‖ ≤ B*beta^n) :
    ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤
      (4*A*B)*beta^n := by
  intro n hn
  have hterm (i : ℕ) (hi : i ∈ Finset.range (n+1)) :
      (n.choose i : ℝ)*‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (n-i) g x‖ ≤
      (n.choose i : ℝ)*(A*B*beta^n) := by
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hni : n-i ≤ 2 := (Nat.sub_le n i).trans hn
    have hc : 0 ≤ (n.choose i : ℝ) := by positivity
    have hp : beta^i*beta^(n-i) = beta^n := by rw [← pow_add,Nat.add_sub_of_le hin]
    calc
      _ ≤ ((n.choose i : ℝ)*(A*beta^i))*(B*beta^(n-i)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hfcap i (hin.trans hn)) hc)
          (hgcap (n-i) hni) (norm_nonneg _) (by positivity)
      _ = (n.choose i : ℝ)*(A*B)*(beta^i*beta^(n-i)) := by ring
      _ = _ := by rw [hp]; ring
  have hc : (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)) ≤ 4 := by
    interval_cases n <;> norm_num [Finset.sum_range_succ]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*‖iteratedFDeriv ℝ i f x‖*
        ‖iteratedFDeriv ℝ (n-i) g x‖ := norm_iteratedFDeriv_smul_le_at_two f g x hf hg n hn
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*(A*B*beta^n) :=
      Finset.sum_le_sum (fun i hi => hterm i hi)
    _ = (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ))*(A*B*beta^n) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 4*(A*B*beta^n) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring
end ProductBudget

section GenericRadiusComposition
variable {E T V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma radius_squared_composite_jets (RR : E → ℝ) (TP : E → T) (Psi : T → V) (x : E)
    (hR : ContDiffAt ℝ ∞ RR x) (hT : ContDiffAt ℝ ∞ TP x)
    (hPsi : ContDiffAt ℝ ∞ Psi (TP x))
    (J M CT beta : ℝ) (hJ : 0 ≤ J) (hM : 0 ≤ M) (hCT : 0 ≤ CT)
    (hr : 0 ≤ RR x) (hb : 1 ≤ beta)
    (hRad : ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k RR x‖ ≤ (J*RR x)*beta^k)
    (hPsiCap : ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k Psi (TP x)‖ ≤ M)
    (hT1 : ‖iteratedFDeriv ℝ 1 TP x‖ ≤ CT)
    (hT2 : ‖iteratedFDeriv ℝ 2 TP x‖ ≤ CT*beta) :
    ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun y => (RR y)^2 • Psi (TP y)) x‖ ≤
        (32*J^2*M*(CT+1)^2)*(RR x)^2*beta^n := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hPcap := small_profile_composition_jets TP Psi x hT hPsi M CT beta hM hCT hb hPsiCap hT1 hT2
  have hRRC (k : ℕ) (hk : k ≤ 2) :
      ‖iteratedFDeriv ℝ k (fun y => (RR y)^2) x‖ ≤ (4*J^2*(RR x)^2)*beta^k := by
    have h := product_jets_two RR RR x hR hR
      (J*RR x) (J*RR x) beta (mul_nonneg hJ hr) (mul_nonneg hJ hr) hb0 hRad hRad k hk
    calc
      _ = ‖iteratedFDeriv ℝ k (fun y => RR y • RR y) x‖ := by
        have he : (fun y : E => (RR y)^2) = (fun y : E => RR y • RR y) := by
          funext y
          simp only [smul_eq_mul,pow_two]
        rw [he]
      _ ≤ (4*(J*RR x)*(J*RR x))*beta^k := h
      _ = _ := by ring
  have hCompGerm : ContDiffAt ℝ ∞ (Psi ∘ TP) x := hPsi.comp x hT
  intro n hn
  have hfin := product_jets_two (fun y => (RR y)^2) (Psi ∘ TP) x
    (hR.pow 2) hCompGerm (4*J^2*(RR x)^2) (2*M*(CT+1)^2) beta
    (by positivity) (by positivity) hb0 hRRC hPcap n hn
  calc
    _ ≤ (4*(4*J^2*(RR x)^2)*(2*M*(CT+1)^2))*beta^n := hfin
    _ = _ := by ring
end GenericRadiusComposition

private lemma first_sums_agree_off_tsupport {E H V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (I : E →L[ℝ] H) (u : R3 → E) (v : Fin 3 → R3) (K : Set R3)
    (B D : R3 → Fin 3 → H →L[ℝ] V) (hsu : tsupport u ⊆ K)
    (heq : ∀ x ∈ K, ∀ l, B x l = D x l) :
    (fun x => ∑ l : Fin 3, B x l (I (fderiv ℝ u x (v l)))) =
      (fun x => ∑ l : Fin 3, D x l (I (fderiv ℝ u x (v l)))) := by
  funext x
  by_cases hx : x ∈ K
  · exact Finset.sum_congr rfl (fun l _ => congrArg
      (fun A : H →L[ℝ] V => A (I (fderiv ℝ u x (v l)))) (heq x hx l))
  · have hxU : x ∉ tsupport u := fun h => hx (hsu h)
    have hd : fderiv ℝ u x = 0 := fderiv_of_notMem_tsupport ℝ hxU
    simp only [hd,ContinuousLinearMap.zero_apply,map_zero,Finset.sum_const_zero]

private lemma contDiffAt_firstFactor {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : Fin 3 → D → ℝ) (Q : Fin 3 → Fin 3 → D → ℝ) (Op : Fin 3 → D → V) (t : D)
    (hX : ∀ m, ContDiffAt ℝ ∞ (X m) t)
    (hQ : ∀ i j, ContDiffAt ℝ ∞ (Q i j) t)
    (hOp : ∀ i, ContDiffAt ℝ ∞ (Op i) t) :
    ContDiffAt ℝ ∞ (fun z => ∑ m : Fin 3, X m z •
      ((∑ j : Fin 3, Q m j z • Op j z)+(∑ i : Fin 3, Q i m z • Op i z))) t := by
  apply ContDiffAt.sum
  intro m _
  exact (hX m).smul ((ContDiffAt.sum (fun j _ => (hQ m j).smul (hOp j))).add
    (ContDiffAt.sum (fun i _ => (hQ i m).smul (hOp i))))

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def firstJetsLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] firstJetsLowNormed
@[instance_reducible] private def firstJetsLowModule : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] firstJetsLowModule
@[instance_reducible] private def firstJetsParameterNormed : NormedAddCommGroup Tpar := inferInstance
attribute [local instance] firstJetsParameterNormed
@[instance_reducible] private def firstJetsParameterModule : NormedSpace ℝ Tpar := inferInstance
attribute [local instance] firstJetsParameterModule
attribute [local irreducible] canonicalLow referenceDensityPrincipalFrameCoefficient
 ActualBalancedFirstPrincipalError.frameEntry ActualHigherSFormation.higherSParam


private structure RadiusProfileTwoJetData (g : MatrixField) (L : ℝ) (K : Set R3) where
  CT : ℝ
  J : ℝ
  CT_pos : 0 < CT
  J_one : 1 ≤ J
  bounds : ∀ q ∈ Icc (0 : ℝ) 1, ∀ δr Ar : ℝ, ∀ p : ℕ,
    0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ x ∈ K,
    1 ≤ actualReferenceBeta g L q δr Ar p x →
    referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
    ‖fderiv ℝ (referenceRadius δr Ar p L) x‖ ≤ 1 →
    ContDiff ℝ ∞ (ActualHigherSFormation.higherSParam L δr Ar p q) ∧
    ‖iteratedFDeriv ℝ 1 (ActualHigherSFormation.higherSParam L δr Ar p q) x‖ ≤ CT ∧
    ‖iteratedFDeriv ℝ 2 (ActualHigherSFormation.higherSParam L δr Ar p q) x‖ ≤
      CT*actualReferenceBeta g L q δr Ar p x ∧
    ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (referenceRadius δr Ar p L) x‖ ≤
      (J*referenceRadius δr Ar p L x)*(actualReferenceBeta g L q δr Ar p x)^n

private theorem exists_radiusProfileTwoJetData (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    Nonempty (RadiusProfileTwoJetData g L K) := by
  obtain ⟨CT,hCT,hT⟩ := exists_reference_radius_parameter_uniform_jet_bounds g hg L hL K hK
  obtain ⟨J1,hJ1,hR1⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 1
  obtain ⟨J2,hJ2,hR2⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 2
  let J : ℝ := 1+J1+J2
  have hJ : 1 ≤ J := by dsimp [J]; linarith
  have hJ1J : J1 ≤ J := by dsimp [J]; linarith
  have hJ2J : J2 ≤ J := by dsimp [J]; linarith
  refine ⟨⟨CT,J,hCT,hJ,?_⟩⟩
  intro q hq δr Ar p hδr hδr1 hAr hp x hx hb hsmall hdR
  have ht := hT q hq δr hδr hδr1 Ar hAr p hp x hx hb hsmall hdR
  have he : ActualHigherSFormation.higherSParam L δr Ar p q =
      (fun z : R3 => ((q,(z,referenceRadius δr Ar p L z)),fderiv ℝ (referenceRadius δr Ar p L) z)) := by
    funext z
    unfold ActualHigherSFormation.higherSParam
    rfl
  have hParam : ContDiff ℝ ∞ (ActualHigherSFormation.higherSParam L δr Ar p q) := by
    rw [he]
    exact ht.1
  have hParam1 : ‖iteratedFDeriv ℝ 1 (ActualHigherSFormation.higherSParam L δr Ar p q) x‖ ≤ CT := by
    rw [he]
    exact ht.2.1
  have hParam2 : ‖iteratedFDeriv ℝ 2 (ActualHigherSFormation.higherSParam L δr Ar p q) x‖ ≤
      CT*actualReferenceBeta g L q δr Ar p x := by
    rw [he]
    exact ht.2.2
  refine ⟨hParam,hParam1,hParam2,?_⟩
  intro n hn
  have hr : 0 < referenceRadius δr Ar p L x := referenceRadius_pos δr Ar p L x hδr hAr
  have hb0 : 0 ≤ actualReferenceBeta g L q δr Ar p x := zero_le_one.trans hb
  interval_cases n
  · rw [norm_iteratedFDeriv_zero,pow_zero,mul_one,Real.norm_eq_abs,abs_of_pos hr]
    exact le_mul_of_one_le_left hr.le hJ
  · have h := (hR1 q hq δr hδr hδr1 Ar hAr p hp x hx).1
    have h' : ‖iteratedFDeriv ℝ 1 (referenceRadius δr Ar p L) x‖ ≤
        J1*referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^1 := by
      simpa only [actualReferenceBeta] using h
    exact h'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hJ1J hr.le) (pow_nonneg hb0 1))
  · have h := (hR2 q hq δr hδr hδr1 Ar hAr p hp x hx).1
    have h' : ‖iteratedFDeriv ℝ 2 (referenceRadius δr Ar p L) x‖ ≤
        J2*referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 := by
      simpa only [actualReferenceBeta] using h
    exact h'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hJ2J hr.le) (pow_nonneg hb0 2))

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "BC" => ActualHigherSCoefficientExtraction.higherSFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact scalar geometry/low-operator factor, with no radius power absorbed into it. -/
def firstCoordinateFactor (g2 : MatrixField) (l : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  ∑ m : Fin 3, ActualBalancedFirstPrincipalError.frameEntry g L m l (t.1.1,t.1.2.1) •
    ((∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 m j • EL j t) +
      ∑ i : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 i m • EL i t)
local notation "Psi" => firstCoordinateFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

lemma contDiffAt_firstCoordinateFactor (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (l : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
    ContDiffAt ℝ ∞ (Psi g2 l) t := by
  have hqx : ContDiff ℝ ∞ (fun z : Tpar => (z.1.1,z.1.2.1)) :=
    (contDiff_fst.fst).prodMk (contDiff_fst.snd.fst)
  have hQ (i j : Fin 3) : ContDiff ℝ ∞ (fun z : Tpar =>
      referenceDensityPrincipalFrameCoefficient g g2 L z.1.1 z.1.2.1 i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp hqx
  have hX (m : Fin 3) : ContDiff ℝ ∞ (fun z : Tpar =>
      ActualBalancedFirstPrincipalError.frameEntry g L m l (z.1.1,z.1.2.1)) :=
    (ActualBalancedFirstPrincipalError.contDiff_frameEntry g hg L m l).comp hqx
  exact contDiffAt_firstFactor
    (fun (m : Fin 3) (z : Tpar) => ActualBalancedFirstPrincipalError.frameEntry g L m l (z.1.1,z.1.2.1))
    (fun (i j : Fin 3) (z : Tpar) => referenceDensityPrincipalFrameCoefficient g g2 L z.1.1 z.1.2.1 i j)
    (fun (j : Fin 3) (z : Tpar) => EL j z) t
    (fun m => (hX m).contDiffAt) (fun i j => (hQ i j).contDiffAt)
    (fun i => Cm.germLow i t ht)

theorem exists_firstCoordinateFactor_uniform_two_jet_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ n : ℕ, n ≤ 2 → ∀ t ∈ ParamRoom δ, ∀ l : Fin 3,
      ‖iteratedFDeriv ℝ n (Psi g2 l) t‖ ≤ M := by
  have hKP : IsCompact (ParamRoom δ) :=
    (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  obtain ⟨M,hM,hcap⟩ := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    (Psi g2) (ParamRoom δ) hKP
    (fun l t ht => contDiffAt_firstCoordinateFactor g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 l t ht) 2
  refine ⟨1+M,by linarith,?_⟩
  intro n hn t ht l
  exact (hcap n hn t ht l).trans (by linarith)

private structure FirstCoordinateFactorData (δ : ℝ) (g2 : MatrixField) where
  M : ℝ
  one_le_M : 1 ≤ M
  cap : ∀ n : ℕ, n ≤ 2 → ∀ t ∈ ParamRoom δ, ∀ l : Fin 3,
    ‖iteratedFDeriv ℝ n (Psi g2 l) t‖ ≤ M
local notation "FactorData" => FirstCoordinateFactorData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

private theorem exists_firstCoordinateFactorData (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : Nonempty (FactorData δ g2) := by
  obtain ⟨M,hM,hCap⟩ := exists_firstCoordinateFactor_uniform_two_jet_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2
  exact ⟨⟨M,hM,hCap⟩⟩

/-- A genuine smooth representative on the native room; equality below is pointwise only. -/
def canonicalFirstCoordinateCoefficient (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) (l : Fin 3) : Half →L[ℝ] Neg :=
  (referenceRadius δr Ar p L x)^2 • Psi g2 l ((Tq δr Ar p q) x)
local notation "BCC" => canonicalFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

private lemma factor_coordinate_radius {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r : ℝ) (X : Fin 3 → ℝ) (a b : Fin 3 → V) :
    r^2 • (∑ m : Fin 3, X m • (a m+b m)) =
      ∑ m : Fin 3, X m • (r^2 • a m+r^2 • b m) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  module

theorem canonicalFirstCoordinateCoefficient_eq_original_at_room
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (x : R3)
    (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) (l : Fin 3) :
    BCC g2 δr Ar p q x l = BC g2 δr Ar p q x l := by
  have heq (j : Fin 3) := ActualHigherSCoefficientBounds.profileLow_eq_canonical
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac
    δr Ar p hδr hAr q hq x hx j
  simp only [canonicalFirstCoordinateCoefficient,firstCoordinateFactor,
    ActualHigherSCoefficientExtraction.higherSFirstCoordinateCoefficient,
    ActualHigherSCoefficientExtraction.firstCoordinateCoefficient,
    ActualHigherSCoefficientExtraction.higherSFirstFrameCoefficient,
    ActualHigherSCoefficientExtraction.firstFrameCoefficient,heq,
    ActualBalancedFirstPrincipalError.frameEntry,ActualHigherSFormation.higherSParam]
  exact factor_coordinate_radius _ _ _ _


private def CanonicalFirstCoordinateJetConclusion (δ : ℝ) (g2 : MatrixField) : Prop :=
    ∃ Cj : ℝ, 0 < Cj ∧ ∀ δr Ar : ℝ, ∀ p : ℕ,
      0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
      1 ≤ actualReferenceBeta g L q δr Ar p x →
      referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
      ∀ l : Fin 3, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun y => BCC g2 δr Ar p q y l) x‖ ≤
        Cj*(referenceRadius δr Ar p L x)^2*(actualReferenceBeta g L q δr Ar p x)^n
local notation "JetConclusion" => CanonicalFirstCoordinateJetConclusion
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

private theorem canonicalFirstCoordinateJetConclusion_of_data
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (D : RadiusProfileTwoJetData g L (closedBall y0 ρ)) (Pj : FactorData δ g2) :
    JetConclusion δ g2 := by
  let M : ℝ := Pj.M
  have hM : 1 ≤ M := Pj.one_le_M
  have hPsi := Pj.cap
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hJpos : 0 < D.J := lt_of_lt_of_le zero_lt_one D.J_one
  have hCTpos : 0 < D.CT := D.CT_pos
  refine ⟨32*D.J^2*M*(D.CT+1)^2,by positivity,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq x hx hb hsmall l n hn
  let RR : R3 → ℝ := referenceRadius δr Ar p L
  let beta : ℝ := actualReferenceBeta g L q δr Ar p x
  have hr : 0 < RR x := referenceRadius_pos δr Ar p L x hδr hAr
  have hxK : x ∈ closedBall y0 ρ := by
    simpa only [ActualHigherSFormation.higherSParam] using hx.1.2.1
  have hdR : ‖fderiv ℝ RR x‖ ≤ 1 := by
    have hmem : fderiv ℝ RR x ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1 := by
      simpa only [ActualHigherSFormation.higherSParam,RR] using hx.2
    exact mem_closedBall_zero_iff.mp hmem
  obtain ⟨hParam,hParam1,hParam2,hRad⟩ := D.bounds q hq δr Ar p hδr hδr1 hAr hp x hxK hb hsmall hdR
  have hR : ContDiff ℝ ∞ RR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hPsigerm := contDiffAt_firstCoordinateFactor
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 l _ hx
  have hfin := radius_squared_composite_jets RR (Tq δr Ar p q) (Psi g2 l) x
    hR.contDiffAt hParam.contDiffAt hPsigerm D.J M D.CT beta
    (zero_le_one.trans D.J_one) (zero_le_one.trans hM) D.CT_pos.le hr.le hb
    hRad (fun k hk => hPsi k hk _ hx l) hParam1 hParam2 n hn
  change ‖iteratedFDeriv ℝ n (fun y => (RR y)^2 • Psi g2 l ((Tq δr Ar p q) y)) x‖ ≤ _
  exact hfin


private theorem canonicalFirstCoordinateJetConclusion_proof
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : JetConclusion δ g2 := by
  have hK : IsCompact (closedBall y0 ρ) := isCompact_closedBall y0 ρ
  obtain ⟨D⟩ := exists_radiusProfileTwoJetData g hg L hL (closedBall y0 ρ) hK
  obtain ⟨Pj⟩ := exists_firstCoordinateFactorData
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2
  exact canonicalFirstCoordinateJetConclusion_of_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 D Pj

theorem exists_canonicalFirstCoordinateCoefficient_uniform_two_jet_bound
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cj : ℝ, 0 < Cj ∧ ∀ δr Ar : ℝ, ∀ p : ℕ,
      0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
      1 ≤ actualReferenceBeta g L q δr Ar p x →
      referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
      ∀ l : Fin 3, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun y => BCC g2 δr Ar p q y l) x‖ ≤
        Cj*(referenceRadius δr Ar p L x)^2*(actualReferenceBeta g L q δr Ar p x)^n := by
  exact canonicalFirstCoordinateJetConclusion_proof
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2


local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "CZ" => ActualHigherSCoefficientExtraction.higherSZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "SN" => ActualHigherSFormation.nativeHigherSNegative
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Equality of whole supported fields; no derivative is inferred from equality on a closed room. -/
theorem actual_higherS_canonical_coordinate_field
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    (fun x => SN g2 q (referenceRadius δr Ar p L) (UF F) x) =
      (fun x => (∑ l : Fin 3, BCC g2 δr Ar p q x l
        (IH (fderiv ℝ (UF F) x (coordinateDirection l))))+CZ g2 δr Ar p q x (UF F x)) := by
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  have hsum := first_sums_agree_off_tsupport IH (UF F) coordinateDirection (tsupport F.val)
    (fun x l => BC g2 δr Ar p q x l) (fun x l => BCC g2 δr Ar p q x l) hRep.2.2.1
    (fun x hx l => (canonicalFirstCoordinateCoefficient_eq_original_at_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac
      g2 δr Ar p hδr hAr q hq x (hTF x hx) l).symm)
  funext x
  have h := ActualHigherSCoefficientExtraction.actual_higherS_coordinate_coefficient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac
    g2 δr Ar p hδr hAr q hq F hTF x
  exact h.trans (congrArg (fun z : Neg => z+CZ g2 δr Ar p q x (UF F x)) (congrFun hsum x))

/-- Differentiation is justified by the preceding global function equality. -/
theorem iteratedFDeriv_actual_higherS_canonical_coordinate_field
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => SN g2 q (referenceRadius δr Ar p L) (UF F) x) =
      iteratedFDeriv ℝ n (fun x => (∑ l : Fin 3, BCC g2 δr Ar p q x l
        (IH (fderiv ℝ (UF F) x (coordinateDirection l))))+CZ g2 δr Ar p q x (UF F x)) := by
  exact congrArg (iteratedFDeriv ℝ n) (actual_higherS_canonical_coordinate_field
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac
    g2 δr Ar p hδr hAr q hq F hTF)


theorem contDiffAt_canonicalFirstCoordinateCoefficient
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (x : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) (l : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => BCC g2 δr Ar p q y l) x := by
  have hR : ContDiff ℝ ∞ (referenceRadius δr Ar p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hParam := ActualHigherSFormation.contDiff_higherSParam
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q
  have hPsi := contDiffAt_firstCoordinateFactor
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 l _ hx
  exact (hR.pow 2).contDiffAt.smul (hPsi.comp x hParam.contDiffAt)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFirstCoefficientJets
