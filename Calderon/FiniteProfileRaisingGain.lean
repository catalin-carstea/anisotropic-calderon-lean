import Calderon.IntegratedProfileConvexity
import Calderon.RaisingCoercivity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
universe u
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.FiniteProfileRaisingGain
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial SphereHarmonic
  WeightedFischerSquare SmoothMetricFrame FischerConnectionTransport
  IntegratedFischerIdentities FiniteRaisingEnergy WeightedRaisingBounds
  ProfileHessianEnergy IntegratedProfileConvexity ReferenceDensityBounds FullCovectorCurvature
attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric finitePolynomialField
variable {ι : Type*} [Fintype ι]

def referenceProfileFrameEnergy (g : MatrixField) (lam δ R L : ℝ) (p : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (k s : ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*
    referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k s x

def referenceFischerMass (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*fischerInner
    (finitePolynomialField b c x) (finitePolynomialField b c x)

lemma referenceProfileFrameEnergy_nonneg (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (k s : ℝ) :
    0 ≤ referenceProfileFrameEnergy g lam δ R L p b c k s := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le
    (Finset.sum_nonneg (fun i _ => fischerInner_self_nonneg _))

lemma referenceFischerMass_nonneg (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) :
    0 ≤ referenceFischerMass g L lam b c := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le (fischerInner_self_nonneg _)

lemma referenceProfileMass_ge_threshold (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (L lam δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) (p : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0)
    (beta0 : ℝ) (hbeta : ∀ x ∈ K, beta0 ≤ referenceProfileNorm g lam δ R p L x) :
    beta0*referenceFischerMass g L lam b c ≤ referenceProfileMass g lam δ R L p b c := by
  have hV := integrable_referenceDensity_fischerPair g hg L lam b b c c hc hc hcompact
  have hM := integrable_referenceProfileNorm_fischerSquare g hg lam δ R L p hδ hR b c hc hcompact
  rw [referenceFischerMass,← integral_const_mul]
  apply integral_mono (hV.const_mul _) hM
  intro x
  by_cases hx : x ∈ K
  · have hh := mul_le_mul_of_nonneg_right (hbeta x hx) (mul_nonneg
      (referenceDensityFamily_pos g hg L (lam,x)).le (fischerInner_self_nonneg (finitePolynomialField b c x)))
    convert hh using 1 <;> ring
  · simp only [hzero x hx,fischerInner_zero_left,mul_zero,le_refl]

theorem referenceProfileRaisingEnergy_gain (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsClosed K)
    (L c0 nu J1 J2 D : ℝ) (hL : 0 < L) (hnu : 0 < nu)
    (hbounds : referenceProfileBounds g K L c0 nu J1 J2 D)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℝ) (hR : 0 < R) (p : ℕ) (hp : 1 ≤ p) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0)
    (a beta0 Ccurv : ℝ) (ha : 0 < a) (hb0 : 1 ≤ beta0) (hC : 0 ≤ Ccurv)
    (hasmall : a ≤ nu/8) (hab : a ≤ beta0) (habsorb : 50*Ccurv ≤ nu*beta0)
    (hbeta : ∀ x ∈ K, beta0 ≤ referenceProfileNorm g lam δ R p L x)
    (hcurv : |referenceIntegratedFullCovectorCurvature g L lam b c| ≤
      Ccurv*((m:ℝ)+1)^2*referenceFischerMass g L lam b c) :
    referenceProfileFrameEnergy g lam δ R L p b c (m+1) 1 /2 +
      (a/4)*(((m:ℝ)+1)+2)*referenceProfileWeightedFrameEnergy g lam δ R L p b c (m+1) 1 +
      nu*((m:ℝ)+1)^3*referenceProfileMass g lam δ R L p b c ≤
      sphereNormalization 3 (m+1)*(referenceRaisingEnergy g L lam b c (referenceLogRadius δ R p L) m -
        referenceLoweringEnergy g L lam b c (referenceLogRadius δ R p L) m) := by
  let n : ℝ := (m:ℝ)+1
  let f := referenceLogRadius δ R p L
  let X := referenceProfileFrameEnergy g lam δ R L p b c n 1
  let Y := (n+2)*referenceProfileWeightedFrameEnergy g lam δ R L p b c n 1
  let G := referenceLoweredWeightedTraceSquare g L lam b c f n (-1)
  let M := referenceProfileMass g lam δ R L p b c
  let V := referenceFischerMass g L lam b c
  let S := referenceLoweredWeightedTraceSquare g L lam b c f n 1
  let H := referenceLoweredHessianEnergy g L lam b c f n
  let J := referenceProfileTraceHessianEnergy g lam δ R L p b c n
  let E := referenceIntegratedFullCovectorCurvature g L lam b c
  have hn : 1 ≤ n := by
    have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
    dsimp only [n]
    linarith
  have hn0 : 0 ≤ n := by linarith
  have hV : 0 ≤ V := referenceFischerMass_nonneg g hg L lam b c
  have hM : 0 ≤ M := referenceProfileMass_nonneg g hg lam δ R L p b c
  have hX : 0 ≤ X := referenceProfileFrameEnergy_nonneg g hg lam δ R L p b c n 1
  have hW := referenceProfileWeightedFrameEnergy_nonneg g hg lam δ R L p b c n 1
  have hY : 0 ≤ Y := mul_nonneg (by linarith) hW
  have hG : 0 ≤ G := referenceLoweredWeightedTraceSquare_nonneg g hg L lam b c f n (-1)
  have hMV : beta0*V ≤ M := referenceProfileMass_ge_threshold g hg K L lam δ R hδ hR p b c hc hcompact hzero beta0 hbeta
  have hthird := referenceProfileFrameEnergy_square_difference g hg L lam δ R p (m+1) hδ hR b c hc hcompact
  have hthird' : referenceProfileFrameEnergy g lam δ R L p b c n (-1) = X+J := by
    simpa only [referenceProfileFrameEnergy,Nat.cast_add,Nat.cast_one,n,X,J] using hthird
  have hfirst := referenceLoweredWeighted_second_integrated_inequality g hg L lam (m+1) (by omega) b hb c f hc
    (contDiff_log_referenceRadius δ R p L hδ hR) hcompact
  have hfirst' : S ≤ n*(X+J)-H+(-E) := by
    have hh : S ≤ n*referenceProfileFrameEnergy g lam δ R L p b c n (-1)-H-E := by
      simpa only [S,n,referenceProfileFrameEnergy,H,E,Nat.cast_add,Nat.cast_one,f] using hfirst
    rw [hthird'] at hh
    linarith
  have hsecond := referenceProfileTrace_convex_uniform_integrated_bound g hg K hK L lam δ R hL hδ hR p (m+1) hp (by omega)
    b hb c hc hcompact hzero a beta0 ha.le (by linarith) hab hbeta
  have hsecond' : S ≤ (n+3-1)*X-a*Y+(2*a/beta0)*G+8*a*n^3*M := by
    convert hsecond using 1 <;> dsimp only [S,n,X,Y,G,M,f,referenceProfileFrameEnergy] <;> push_cast <;> ring
  have hhH := referenceProfile_loweredHessianEnergy_le g hg K L c0 nu J1 J2 D hbounds lam hlam δ hδ hδ1 R hR p hp (m+1) b hb c hc hcompact hzero
  have hH : H ≤ -2*nu*n^2*M := by
    simpa only [H,n,M,f,Nat.cast_add,Nat.cast_one,mul_assoc] using hhH
  have hhJ := referenceProfileTraceHessianEnergy_le g hg K L c0 nu J1 J2 D hbounds lam hlam δ hδ hδ1 R hR p hp (m+1) b c hc hcompact hzero
  have hJ : J ≤ -6*nu*n*M := by
    simpa only [J,n,M,Nat.cast_add,Nat.cast_one,mul_assoc] using hhJ
  have hJ0 : J ≤ 0 := by
    have hh : 0 ≤ 6*nu*n*M := by positivity
    linarith only [hJ,hh]
  have hR2 : -E ≤ (5*Ccurv)*n^2*V := by
    have hh : -E ≤ Ccurv*n^2*V := (neg_le_abs E).trans hcurv
    have hpC : 0 ≤ Ccurv*n^2*V := by positivity
    linarith
  have hR3 : -(5*Ccurv)*n^3*V ≤ (3+2*n)*E := by
    have hE : -(Ccurv*n^2*V) ≤ E := by linarith [(neg_le_abs E).trans hcurv]
    have hcE := mul_le_mul_of_nonneg_left hE (show 0 ≤ 3+2*n by positivity)
    have hcost : (3+2*n)*(Ccurv*n^2*V) ≤ (5*Ccurv)*n^3*V := by
      nlinarith only [mul_nonneg (show 0 ≤ n-1 by linarith) (show 0 ≤ 3*Ccurv*n^2*V by positivity)]
    linarith
  have hbound := raising_form_lower_bound (n:=3) (k:=n) (c₀:=nu) (c₁:=a) (C:=5*Ccurv) (β:=beta0)
    (X:=X) (Y:=Y) (G:=G) (W:=M) (V:=V) (F:=S) (H:=H) (T:=J) (R₂:=-E) (R₃:=(3+2*n)*E)
    (by norm_num) hn hnu ha (by positivity) hb0 hasmall hab (by linarith) hMV hX hY hG hM hV hfirst' hsecond' hJ0 hH hR2 hR3
  have henergy := referenceRaisingEnergy_sub_loweringEnergy_reduced hF g hg L lam m b hb c f hc
    (contDiff_log_referenceRadius δ R p L hδ hR) hcompact
  have hN := sphereNormalization_pos (n:=3) (by norm_num : 0 < 3) (m+1)
  have hExact : sphereNormalization 3 (m+1)*(referenceRaisingEnergy g L lam b c f m-referenceLoweringEnergy g L lam b c f m) =
      (2+2/(n+3/2-1))*((n+3/2-1)*X-S-(n+3/2-1)*H)+2*G+(3+2*n)*E := by
    have henergy' : referenceRaisingEnergy g L lam b c f m-referenceLoweringEnergy g L lam b c f m =
        ((3+2*n)*(X-(4/(4*(m:ℝ)+6))*S-H)+2*G+(3+2*n)*E)/sphereNormalization 3 (m+1) := henergy
    have hden : 4*(m:ℝ)+6 = 4*(n+3/2-1) := by dsimp only [n]; ring
    rw [henergy',hden]
    have hd : n+3/2-1 ≠ 0 := by linarith
    field_simp [hN.ne',hd]
    <;> ring_nf
    <;> field_simp [show 1+n*2 ≠ 0 by linarith]
    <;> ring
  rw [← hExact] at hbound
  simpa only [X,Y,n,M,f,referenceProfileFrameEnergy,Nat.cast_add,Nat.cast_one,mul_assoc] using hbound

theorem exists_referenceIntegratedCurvature_allFinite_uniform_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : Type u) [Fintype τ], ∀ hF : SphereFischerInner,
      ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ k : ℕ, 1 ≤ k →
      ∀ b : τ → MvPolynomial (Fin 3) ℝ, (∀ j, b j ∈ harmonicHomogeneous k) →
      ∀ c : R3 → τ → ℝ, ContDiff ℝ ∞ c → HasCompactSupport c →
      (∀ x ∉ K, finitePolynomialField b c x = 0) →
      |referenceIntegratedFullCovectorCurvature g L lam b c| ≤
        C*(k:ℝ)^2*referenceFischerMass g L lam b c := by
  obtain ⟨C,hC,hbound⟩ := exists_referenceFullCovectorCurvatureContraction_uniform_fischer_bound g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro τ inst hF lam hlam k hk b hb c hc hcompact hzero
  have hE := integrable_referenceFullCovectorCurvature g hg L lam b c hc hcompact
  have hU := integrable_referenceDensity_fischerPair g hg L lam b b c c hc hc hcompact
  have hp (x : R3) : |referenceDensityFamily g L (lam,x)*
      referenceFullCovectorCurvatureContraction g L lam x (referenceMetricGramFrame g L (lam,x)) (finitePolynomialField b c x)| ≤
      (C*(k:ℝ)^2)*(referenceDensityFamily g L (lam,x)*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
    by_cases hx : x ∈ K
    · rw [abs_mul,abs_of_pos (referenceDensityFamily_pos g hg L (lam,x))]
      calc
        _ ≤ referenceDensityFamily g L (lam,x)*(C*(k:ℝ)^2*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) :=
          mul_le_mul_of_nonneg_left (hbound hF lam hlam x hx _
            (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)) k hk _
            (finitePolynomialField_harmonicHomogeneous k b hb c x))
            (referenceDensityFamily_pos g hg L (lam,x)).le
        _ = _ := by ring
    · rw [hzero x hx,referenceFullCovectorCurvatureContraction_zero]
      simp only [fischerInner_zero_left,mul_zero,abs_zero,le_refl]
  calc
    _ ≤ ∫ x : R3, |referenceDensityFamily g L (lam,x)*referenceFullCovectorCurvatureContraction g L lam x
      (referenceMetricGramFrame g L (lam,x)) (finitePolynomialField b c x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x : R3, (C*(k:ℝ)^2)*(referenceDensityFamily g L (lam,x)*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) :=
      integral_mono hE.abs (hU.const_mul _) hp
    _ = _ := integral_const_mul _ _

theorem exists_referenceProfileRaisingEnergy_uniform_gain (g : MatrixField)
    (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L a nu : ℝ, 0 < L ∧ 0 < a ∧ 0 < nu ∧
      ∀ ε : ℝ, 0 < ε → ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
          referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x^2 ≤ ε) ∧
        ∀ (τ : Type u) [Fintype τ], ∀ hF : SphereFischerInner,
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ m : ℕ, ∀ b : τ → MvPolynomial (Fin 3) ℝ,
          (∀ j, b j ∈ harmonicHomogeneous (m+1)) →
          ∀ c : R3 → τ → ℝ, ContDiff ℝ ∞ c → HasCompactSupport c →
          (∀ x ∉ K, finitePolynomialField b c x = 0) →
          referenceProfileFrameEnergy g lam δ R L p b c (m+1) 1 /2 +
            (a/4)*(((m:ℝ)+1)+2)*referenceProfileWeightedFrameEnergy g lam δ R L p b c (m+1) 1 +
            nu*((m:ℝ)+1)^3*referenceProfileMass g lam δ R L p b c ≤
            sphereNormalization 3 (m+1)*(referenceRaisingEnergy g L lam b c (referenceLogRadius δ R p L) m -
              referenceLoweringEnergy g L lam b c (referenceLogRadius δ R p L) m) := by
  obtain ⟨L,c0,nu,J1,J2,D,hL,hc0,hnu,hJ1,hJ2,hD,hbounds⟩ := exists_referenceProfileBounds g hg K hK
  obtain ⟨C,hC,hcurv⟩ := exists_referenceIntegratedCurvature_allFinite_uniform_bound.{u} g hg L hL K hK
  let a := min (1:ℝ) (nu/8)
  let beta0 := max (1:ℝ) (50*C/nu)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hasmall : a ≤ nu/8 := min_le_right _ _
  have ha1 : a ≤ 1 := min_le_left _ _
  have hb0 : 1 ≤ beta0 := le_max_left _ _
  have hab : a ≤ beta0 := ha1.trans hb0
  have habsorb : 50*C ≤ nu*beta0 := by
    have hh := (div_le_iff₀ hnu).mp (le_max_right (1:ℝ) (50*C/nu))
    simpa only [beta0,mul_comm] using hh
  refine ⟨L,a,nu,hL,ha,hnu,?_⟩
  intro ε hε
  obtain ⟨p,hp,R,hR,hprofile⟩ := referenceProfileBounds_choose_degree_radius g K L c0 nu J1 J2 D hc0 hbounds beta0 ε hε
  refine ⟨p,hp,R,hR,?_,?_⟩
  · intro lam hlam δ hδ hδ1 x hx
    exact (hprofile lam hlam δ hδ hδ1 x hx).2
  · intro τ inst hF lam hlam δ hδ hδ1 m b hb c hc hcompact hzero
    have hhcurv : |referenceIntegratedFullCovectorCurvature g L lam b c| ≤
        C*((m:ℝ)+1)^2*referenceFischerMass g L lam b c := by
      simpa only [Nat.cast_add,Nat.cast_one] using hcurv τ hF lam hlam (m+1) (by omega) b hb c hc hcompact hzero
    exact referenceProfileRaisingEnergy_gain hF g hg K hK.isClosed L c0 nu J1 J2 D hL hnu hbounds
      lam hlam δ hδ hδ1 R hR p (by omega) m b hb c hc hcompact hzero a beta0 C ha hb0 hC.le
      hasmall hab habsorb (fun x hx => (hprofile lam hlam δ hδ hδ1 x hx).1) hhcurv

end OAI.AnisotropicCalderon.FiniteProfileRaisingGain
