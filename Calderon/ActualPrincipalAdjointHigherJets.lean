import Calderon.ActualPrincipalAdjointDerivative
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualPrincipalAdjointHigherJets
open PrincipalCommutator ScalarBaseAdjoint ReferenceDensityBounds PerturbedDensityAdjoint
  ConformalDepth ActualScalarPrincipalAdjoint ActualPerturbedDefect
  ActualPrincipalErrorCoefficient ActualPrincipalAdjointDerivative NaturalAngularAdjoint

/-- The forty literal ordered coordinate jets of a scalar function, through order three. -/
def CoordinateThreeJetBound (f : R3 → ℝ) (x : R3) (A : ℝ) : Prop :=
  |f x| ≤ A ∧
  (∀ i : Fin 3, |directionalFDeriv (coordinateDirection i) f x| ≤ A) ∧
  (∀ i j : Fin 3, |directionalFDeriv (coordinateDirection j)
    (directionalFDeriv (coordinateDirection i) f) x| ≤ A) ∧
  ∀ i j k : Fin 3, |directionalFDeriv (coordinateDirection k)
    (directionalFDeriv (coordinateDirection j)
      (directionalFDeriv (coordinateDirection i) f)) x| ≤ A

lemma coordinateThreeJetBound_twoJetBound (f : R3 → ℝ) (x : R3) (A : ℝ)
    (h : CoordinateThreeJetBound f x A) (i j : Fin 3) :
    TwoJetBound (coordinateDirection i) (coordinateDirection j) f x A :=
  ⟨h.1,h.2.1 i,h.2.1 j,h.2.2.1 i j⟩

lemma coordinateThreeJetBound_mono (f : R3 → ℝ) (x : R3) (A B : ℝ)
    (h : CoordinateThreeJetBound f x A) (hab : A ≤ B) :
    CoordinateThreeJetBound f x B :=
  ⟨h.1.trans hab,fun i => (h.2.1 i).trans hab,
    fun i j => (h.2.2.1 i j).trans hab,fun i j k => (h.2.2.2 i j k).trans hab⟩

abbrev ThreeJetTag := Sum JetTag (Fin 3 × Fin 3 × Fin 3)

def coordinateThreeJetFamily (F : ℝ × R3 → ℝ) : ThreeJetTag → ℝ × R3 → ℝ
  | .inl t => coordinateJetFamily F t
  | .inr (i,j,k) => familyDirectionalDeriv k
      (familyDirectionalDeriv j (familyDirectionalDeriv i F))

lemma continuous_coordinateThreeJetFamily (F : ℝ × R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) (t : ThreeJetTag) :
    Continuous (coordinateThreeJetFamily F t) := by
  rcases t with t | ⟨i,j,k⟩
  · exact continuous_coordinateJetFamily F hF t
  · exact (contDiff_familyDirectionalDeriv k _
      (contDiff_familyDirectionalDeriv j _ (contDiff_familyDirectionalDeriv i F hF))).continuous

/-- Fixed background constants are selected before all radius and perturbation parameters. -/
theorem exists_referenceBackground_uniform_three_jet_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ t : BackgroundTag, CoordinateThreeJetBound
        (fun y => referenceBackgroundFamily g L t (lam,y)) x M := by
  obtain ⟨M,hM,hbound⟩ := exists_uniform_bound_finite_family
    (fun t : BackgroundTag × ThreeJetTag =>
      coordinateThreeJetFamily (referenceBackgroundFamily g L t.1) t.2)
    (fun t => continuous_coordinateThreeJetFamily _
      (contDiff_referenceBackgroundFamily g hg L t.1) t.2) K hK
  refine ⟨M,hM,?_⟩
  intro lam hlam x hx t
  refine ⟨?_,?_,?_,?_⟩
  · exact hbound lam hlam x hx (t,.inl (.inl ()))
  · intro i
    exact hbound lam hlam x hx (t,.inl (.inr (.inl i)))
  · intro i j
    exact hbound lam hlam x hx (t,.inl (.inr (.inr (i,j))))
  · intro i j k
    exact hbound lam hlam x hx (t,.inr (i,j,k))

/-- Actual orthonormal-frame entries have the same finite, fixed three-jet control. -/
theorem exists_referenceFrame_uniform_three_jet_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ F : ℝ, 1 ≤ F ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ l k : Fin 3, CoordinateThreeJetBound
        (fun y => referenceFrameEntryFamily g L l k (lam,y)) x F := by
  obtain ⟨F,hF,hbound⟩ := exists_uniform_bound_finite_family
    (fun t : (Fin 3 × Fin 3) × ThreeJetTag =>
      coordinateThreeJetFamily (referenceFrameEntryFamily g L t.1.1 t.1.2) t.2)
    (fun t => continuous_coordinateThreeJetFamily _
      (contDiff_referenceFrameEntryFamily g hg L t.1.1 t.1.2) t.2) K hK
  refine ⟨F,hF,?_⟩
  intro lam hlam x hx l k
  refine ⟨?_,?_,?_,?_⟩
  · exact hbound lam hlam x hx ((l,k),.inl (.inl ()))
  · intro i
    exact hbound lam hlam x hx ((l,k),.inl (.inr (.inl i)))
  · intro i j
    exact hbound lam hlam x hx ((l,k),.inl (.inr (.inr (i,j))))
  · intro i j m
    exact hbound lam hlam x hx ((l,k),.inr (i,j,m))

lemma abs_coordinate_third_le (i j k : Fin 3) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : R3) :
    |directionalFDeriv (coordinateDirection k)
      (directionalFDeriv (coordinateDirection j)
        (directionalFDeriv (coordinateDirection i) f)) x| ≤
      ‖iteratedFDeriv ℝ 3 f x‖ := by
  have hs := abs_coordinate_second_le j k (directionalFDeriv (coordinateDirection i) f)
    (contDiff_directionalFDeriv (coordinateDirection i) f hf) x
  have ht := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ f) (c := coordinateDirection i) (x := x) (n := 2)
    ((hf.fderiv_right (m := ∞) (by simp)).contDiffAt) (by simp)
  have he : ‖iteratedFDeriv ℝ 2 (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 3 f x‖ :=
    norm_iteratedFDeriv_fderiv
  apply hs.trans
  change ‖iteratedFDeriv ℝ 2 (fun y => (fderiv ℝ f y) (coordinateDirection i)) x‖ ≤ _
  simpa only [norm_coordinateDirection,one_mul,mul_one,he] using ht

lemma directional_third_mul (i j k : R3) (f g : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R3) :
    directionalFDeriv k (directionalFDeriv j
      (directionalFDeriv i (fun y => f y*g y))) x =
      directionalFDeriv k (directionalFDeriv j (directionalFDeriv i f)) x*g x +
      directionalFDeriv j (directionalFDeriv i f) x*directionalFDeriv k g x +
      directionalFDeriv k (directionalFDeriv i f) x*directionalFDeriv j g x +
      directionalFDeriv i f x*directionalFDeriv k (directionalFDeriv j g) x +
      directionalFDeriv k (directionalFDeriv j f) x*directionalFDeriv i g x +
      directionalFDeriv j f x*directionalFDeriv k (directionalFDeriv i g) x +
      directionalFDeriv k f x*directionalFDeriv j (directionalFDeriv i g) x +
      f x*directionalFDeriv k (directionalFDeriv j (directionalFDeriv i g)) x := by
  have he : directionalFDeriv j (directionalFDeriv i (fun y => f y*g y)) =
      fun y => directionalFDeriv j (directionalFDeriv i f) y*g y +
        directionalFDeriv i f y*directionalFDeriv j g y +
        directionalFDeriv j f y*directionalFDeriv i g y +
        f y*directionalFDeriv j (directionalFDeriv i g) y :=
    funext (directional_second_mul i j f g hf hg)
  have hfi := contDiff_directionalFDeriv i f hf
  have hfj := contDiff_directionalFDeriv j f hf
  have hfji := contDiff_directionalFDeriv j _ hfi
  have hgi := contDiff_directionalFDeriv i g hg
  have hgj := contDiff_directionalFDeriv j g hg
  have hgji := contDiff_directionalFDeriv j _ hgi
  rw [he, directionalFDeriv_add k _ _
      (((hfji.mul hg).add (hfi.mul hgj)).add (hfj.mul hgi)) (hf.mul hgji),
    directionalFDeriv_add k _ _ ((hfji.mul hg).add (hfi.mul hgj)) (hfj.mul hgi),
    directionalFDeriv_add k _ _ (hfji.mul hg) (hfi.mul hgj),
    directional_mul k _ _ hfji hg, directional_mul k _ _ hfi hgj,
    directional_mul k _ _ hfj hgi, directional_mul k _ _ hf hgji]
  ring

lemma directional_third_add (i j k : R3) (f g : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R3) :
    directionalFDeriv k (directionalFDeriv j
      (directionalFDeriv i (fun y => f y+g y))) x =
      directionalFDeriv k (directionalFDeriv j (directionalFDeriv i f)) x +
      directionalFDeriv k (directionalFDeriv j (directionalFDeriv i g)) x := by
  have he : directionalFDeriv j (directionalFDeriv i (fun y => f y+g y)) =
      fun y => directionalFDeriv j (directionalFDeriv i f) y +
        directionalFDeriv j (directionalFDeriv i g) y :=
    funext (directional_second_add i j f g hf hg)
  rw [he, directionalFDeriv_add k _ _
    (contDiff_directionalFDeriv j _ (contDiff_directionalFDeriv i f hf))
    (contDiff_directionalFDeriv j _ (contDiff_directionalFDeriv i g hg))]

lemma coordinateThreeJetBound_add (f g : R3 → ℝ) (x : R3) (A B : ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hF : CoordinateThreeJetBound f x A) (hG : CoordinateThreeJetBound g x B) :
    CoordinateThreeJetBound (fun y => f y+g y) x (A+B) := by
  refine ⟨(abs_add_le _ _).trans (add_le_add hF.1 hG.1),?_,?_,?_⟩
  · intro i
    rw [directionalFDeriv_add _ _ _ hf hg]
    exact (abs_add_le _ _).trans (add_le_add (hF.2.1 i) (hG.2.1 i))
  · intro i j
    rw [directional_second_add _ _ _ _ hf hg]
    exact (abs_add_le _ _).trans (add_le_add (hF.2.2.1 i j) (hG.2.2.1 i j))
  · intro i j k
    rw [directional_third_add _ _ _ _ _ hf hg]
    exact (abs_add_le _ _).trans (add_le_add (hF.2.2.2 i j k) (hG.2.2.2 i j k))

lemma abs_eight_add_le (a b c d e f g h : ℝ) :
    |a+b+c+d+e+f+g+h| ≤ |a|+|b|+|c|+|d|+|e|+|f|+|g|+|h| := by
  linarith [abs_add_le a b,abs_add_le (a+b) c,abs_add_le (a+b+c) d,
    abs_add_le (a+b+c+d) e,abs_add_le (a+b+c+d+e) f,
    abs_add_le (a+b+c+d+e+f) g,abs_add_le (a+b+c+d+e+f+g) h]

lemma product_three_jet_bounds (f g : R3 → ℝ) (x : R3) (A B : ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : CoordinateThreeJetBound f x A) (hG : CoordinateThreeJetBound g x B) :
    |f x*g x| ≤ A*B ∧
    (∀ i : Fin 3, |directionalFDeriv (coordinateDirection i) (fun y => f y*g y) x| ≤ 2*A*B) ∧
    (∀ i j : Fin 3, |directionalFDeriv (coordinateDirection j)
      (directionalFDeriv (coordinateDirection i) (fun y => f y*g y)) x| ≤ 4*A*B) ∧
    ∀ i j k : Fin 3, |directionalFDeriv (coordinateDirection k)
      (directionalFDeriv (coordinateDirection j)
        (directionalFDeriv (coordinateDirection i) (fun y => f y*g y))) x| ≤ 8*A*B := by
  have hab (u v : ℝ) (hu : |u| ≤ A) (hv : |v| ≤ B) : |u*v| ≤ A*B := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) hA
  refine ⟨hab _ _ hF.1 hG.1,?_,?_,?_⟩
  · intro i
    exact (product_two_jet_bounds _ _ f g x A B hf hg hA hB
      (coordinateThreeJetBound_twoJetBound f x A hF i i)
      (coordinateThreeJetBound_twoJetBound g x B hG i i)).2.1
  · intro i j
    exact (product_two_jet_bounds _ _ f g x A B hf hg hA hB
      (coordinateThreeJetBound_twoJetBound f x A hF i j)
      (coordinateThreeJetBound_twoJetBound g x B hG i j)).2.2.2
  · intro i j k
    rw [directional_third_mul _ _ _ f g hf hg]
    have h1 := hab _ _ (hF.2.2.2 i j k) hG.1
    have h2 := hab _ _ (hF.2.2.1 i j) (hG.2.1 k)
    have h3 := hab _ _ (hF.2.2.1 i k) (hG.2.1 j)
    have h4 := hab _ _ (hF.2.1 i) (hG.2.2.1 j k)
    have h5 := hab _ _ (hF.2.2.1 j k) (hG.2.1 i)
    have h6 := hab _ _ (hF.2.1 j) (hG.2.2.1 i k)
    have h7 := hab _ _ (hF.2.1 k) (hG.2.2.1 i j)
    have h8 := hab _ _ hF.1 (hG.2.2.2 i j k)
    exact (abs_eight_add_le _ _ _ _ _ _ _ _).trans (by linarith)

lemma product_third_scaled_bound (i j k : Fin 3) (r b : R3 → ℝ) (x : R3)
    (hr : ContDiff ℝ ∞ r) (hb : ContDiff ℝ ∞ b)
    (R0 R1 R2 R3 B : ℝ) (hR0 : 0 ≤ R0) (hR1 : 0 ≤ R1)
    (hR2 : 0 ≤ R2) (hR3 : 0 ≤ R3)
    (hr0 : |r x| ≤ R0)
    (hr1 : ∀ l : Fin 3, |directionalFDeriv (coordinateDirection l) r x| ≤ R1)
    (hr2 : ∀ l m : Fin 3, |directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection l) r) x| ≤ R2)
    (hr3 : |directionalFDeriv (coordinateDirection k)
      (directionalFDeriv (coordinateDirection j)
        (directionalFDeriv (coordinateDirection i) r)) x| ≤ R3)
    (hb0 : |b x| ≤ B)
    (hb1 : ∀ l : Fin 3, |directionalFDeriv (coordinateDirection l) b x| ≤ 2*B)
    (hb2 : ∀ l m : Fin 3, |directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection l) b) x| ≤ 4*B)
    (hb3 : |directionalFDeriv (coordinateDirection k)
      (directionalFDeriv (coordinateDirection j)
        (directionalFDeriv (coordinateDirection i) b)) x| ≤ 8*B) :
    |directionalFDeriv (coordinateDirection k)
      (directionalFDeriv (coordinateDirection j)
        (directionalFDeriv (coordinateDirection i) (fun y => r y*b y))) x| ≤
      R3*B+6*R2*B+12*R1*B+8*R0*B := by
  have hab (u v A C : ℝ) (hA : 0 ≤ A) (hu : |u| ≤ A) (hv : |v| ≤ C) :
      |u*v| ≤ A*C := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) hA
  rw [directional_third_mul _ _ _ r b hr hb]
  have h1 := hab _ _ _ _ hR3 hr3 hb0
  have h2 := hab _ _ _ _ hR2 (hr2 i j) (hb1 k)
  have h3 := hab _ _ _ _ hR2 (hr2 i k) (hb1 j)
  have h4 := hab _ _ _ _ hR1 (hr1 i) (hb2 j k)
  have h5 := hab _ _ _ _ hR2 (hr2 j k) (hb1 i)
  have h6 := hab _ _ _ _ hR1 (hr1 j) (hb2 i k)
  have h7 := hab _ _ _ _ hR1 (hr1 k) (hb2 i j)
  have h8 := hab _ _ _ _ hR0 hr0 hb3
  exact (abs_eight_add_le _ _ _ _ _ _ _ _).trans (by linarith)

/-- A derived three-jet coefficient estimate from ordinary finite jets. -/
theorem density_principal_third_bound (mu r q h : R3 → ℝ)
    (hm : ContDiff ℝ ∞ mu) (hr : ContDiff ℝ ∞ r)
    (hq : ContDiff ℝ ∞ q) (hh : ContDiff ℝ ∞ h) (x : R3)
    (M J1 J2 J3 beta eps : ℝ) (hM : 1 ≤ M)
    (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2) (hJ3 : 0 ≤ J3)
    (hb : 1 ≤ beta) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hpos : 0 < r x)
    (hsmall : r x*beta^2 ≤ eps)
    (hmjet : CoordinateThreeJetBound mu x M)
    (hqjet : CoordinateThreeJetBound q x M)
    (hhjet : CoordinateThreeJetBound h x (eps*r x))
    (hr1 : ∀ i : Fin 3, |directionalFDeriv (coordinateDirection i) r x| ≤ J1*r x*beta)
    (hr2 : ∀ i j : Fin 3, |directionalFDeriv (coordinateDirection j)
      (directionalFDeriv (coordinateDirection i) r) x| ≤ J2*r x*beta^2)
    (hr3 : ∀ i j k : Fin 3, |directionalFDeriv (coordinateDirection k)
      (directionalFDeriv (coordinateDirection j)
        (directionalFDeriv (coordinateDirection i) r)) x| ≤ J3*r x*beta^3) :
    ∀ i j k : Fin 3, |directionalFDeriv (coordinateDirection k)
      (directionalFDeriv (coordinateDirection j)
        (directionalFDeriv (coordinateDirection i) (densityPrincipalEntry mu r q h))) x| ≤
      (J3+6*J2+12*J1+8)*M*(M+1)*eps*beta := by
  have hb0 : 0 ≤ beta := by linarith
  have hb2 : 1 ≤ beta^2 := by nlinarith [sq_nonneg (beta-1)]
  have hb3 : 1 ≤ beta^3 := by nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb2)]
  have hp1 : beta ≤ beta^3 := by nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb2)]
  have hp2 : beta^2 ≤ beta^3 := by nlinarith [mul_nonneg (sq_nonneg beta) (sub_nonneg.mpr hb)]
  have hre : r x ≤ eps := by nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hb2)]
  have hepr : eps*r x ≤ 1 := by nlinarith
  have hh1 := coordinateThreeJetBound_mono h x _ 1 hhjet hepr
  have hsum := coordinateThreeJetBound_add q h x M 1 hq hh hqjet hh1
  let b : R3 → ℝ := fun y => mu y*(q y+h y)
  have hbs : ContDiff ℝ ∞ b := hm.mul (hq.add hh)
  obtain ⟨hbv,hbd,hbdd,hbddd⟩ := product_three_jet_bounds mu (fun y => q y+h y) x
    M (M+1) hm (hq.add hh) (by linarith) (by linarith) hmjet hsum
  have he : densityPrincipalEntry mu r q h = fun y => r y*b y := by
    funext y
    unfold densityPrincipalEntry principalEntry b
    ring
  have hr0' : |r x| ≤ r x*beta^3 := by
    rw [abs_of_pos hpos]
    nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hb3)]
  have hr1' (i : Fin 3) : |directionalFDeriv (coordinateDirection i) r x| ≤ J1*r x*beta^3 :=
    (hr1 i).trans (mul_le_mul_of_nonneg_left hp1 (by positivity))
  have hr2' (i j : Fin 3) : |directionalFDeriv (coordinateDirection j)
      (directionalFDeriv (coordinateDirection i) r) x| ≤ J2*r x*beta^3 :=
    (hr2 i j).trans (mul_le_mul_of_nonneg_left hp2 (by positivity))
  have hs : r x*beta^3 ≤ eps*beta := by
    have ht := mul_le_mul_of_nonneg_right hsmall hb0
    nlinarith
  intro i j k
  rw [he]
  have ht := product_third_scaled_bound i j k r b x hr hbs
    (r x*beta^3) (J1*r x*beta^3) (J2*r x*beta^3) (J3*r x*beta^3)
    (M*(M+1)) (by positivity) (by positivity) (by positivity) (by positivity)
    hr0' hr1' hr2' (hr3 i j k) hbv
    (fun a => by simpa only [b,mul_assoc] using hbd a)
    (fun a c => by simpa only [b,mul_assoc] using hbdd a c)
    (by simpa only [b,mul_assoc] using hbddd i j k)
  have hu : |directionalFDeriv (coordinateDirection k)
      (directionalFDeriv (coordinateDirection j)
        (directionalFDeriv (coordinateDirection i) (fun y => r y*b y))) x| ≤
      ((J3+6*J2+12*J1+8)*M*(M+1))*(r x*beta^3) := by
    convert ht using 1 <;> ring
  exact hu.trans (by
    have hv := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ (J3+6*J2+12*J1+8)*M*(M+1) by positivity)
    convert hv using 1 <;> ring)

/-- Third jets of the actual rQ and its actual base-density multiple have the source eps beta size. -/
theorem exists_actual_principal_third_uniform_bounds (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C3 : ℝ, 0 < C3 ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j, CoordinateThreeJetBound (fun y => h y i j) x
        (eps * referenceRadius δ R p L x)) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i j k l m,
        |directionalFDeriv (coordinateDirection m) (directionalFDeriv (coordinateDirection l)
          (directionalFDeriv (coordinateDirection k)
            (fun y => referenceDensityFamily g L (lam,y) *
              actualPrincipalMatrix g L lam δ R p h y i j))) x| ≤ C3*eps*beta ∧
        |directionalFDeriv (coordinateDirection m) (directionalFDeriv (coordinateDirection l)
          (directionalFDeriv (coordinateDirection k)
            (fun y => actualPrincipalMatrix g L lam δ R p h y i j))) x| ≤ C3*eps*beta := by
  obtain ⟨M,hM,hbackground⟩ := exists_referenceBackground_uniform_three_jet_bound g hg L K hK
  obtain ⟨J1,hJ1,hjet1⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 1
  obtain ⟨J2,hJ2,hjet2⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 2
  obtain ⟨J3,hJ3,hjet3⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 3
  refine ⟨(J3+6*J2+12*J1+8)*M*(M+1),by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet beta hb hsmall i j k l m
  let r : R3 → ℝ := referenceRadius δ R p L
  let mu : R3 → ℝ := fun y => referenceDensityFamily g L (lam,y)
  let q : R3 → ℝ := fun y => referenceInverseEntryFamily g L i j (lam,y)
  have hslice : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp hslice
  have hq : ContDiff ℝ ∞ q := (contDiff_referenceInverseEntryFamily g hg L i j).comp hslice
  have hmu : CoordinateThreeJetBound mu x M := by
    simpa [referenceBackgroundFamily,mu] using
      hbackground lam hlam x hx (.inl 0)
  have hqq : CoordinateThreeJetBound q x M := hbackground lam hlam x hx (.inr (i,j))
  have hr : ContDiff ℝ ∞ r := contDiff_referenceRadius_actual δ R p L hδ hR
  have h1 := (hjet1 lam hlam δ hδ hδ1 R hR p hp x hx).1
  have h2 := (hjet2 lam hlam δ hδ hδ1 R hR p hp x hx).1
  have h3 := (hjet3 lam hlam δ hδ hδ1 R hR p hp x hx).1
  have hr1 (a : Fin 3) : |directionalFDeriv (coordinateDirection a) r x| ≤ J1*r x*beta := by
    simpa only [pow_one] using (abs_coordinate_first_le a r x).trans h1
  have hr2 (a b : Fin 3) : |directionalFDeriv (coordinateDirection b)
      (directionalFDeriv (coordinateDirection a) r) x| ≤ J2*r x*beta^2 :=
    (abs_coordinate_second_le a b r hr x).trans h2
  have hr3 (a b c : Fin 3) : |directionalFDeriv (coordinateDirection c)
      (directionalFDeriv (coordinateDirection b)
        (directionalFDeriv (coordinateDirection a) r)) x| ≤ J3*r x*beta^3 :=
    (abs_coordinate_third_le a b c r hr x).trans h3
  have hc : CoordinateThreeJetBound (fun _ : R3 => (1 : ℝ)) x M := by
    unfold CoordinateThreeJetBound directionalFDeriv
    simp only [fderiv_const_apply,ContinuousLinearMap.zero_apply,abs_zero,abs_one]
    exact ⟨hM,fun _ => by linarith,fun _ _ => by linarith,fun _ _ _ => by linarith⟩
  have ht := density_principal_third_bound mu r q (fun y => h y i j)
    hm hr hq (hh i j) x M J1 J2 J3 beta eps hM hJ1.le hJ2.le hJ3.le hb heps heps1
    (referenceRadius_pos δ R p L x hδ hR) hsmall hmu hqq (hhjet i j) hr1 hr2 hr3 k l m
  have hu := density_principal_third_bound (fun _ : R3 => (1 : ℝ)) r q (fun y => h y i j)
    contDiff_const hr hq (hh i j) x M J1 J2 J3 beta eps hM hJ1.le hJ2.le hJ3.le hb heps heps1
    (referenceRadius_pos δ R p L x hδ hR) hsmall hc hqq (hhjet i j) hr1 hr2 hr3 k l m
  constructor
  · have hew : densityPrincipalEntry mu r q (fun y => h y i j) =
        fun y => referenceDensityFamily g L (lam,y) * actualPrincipalMatrix g L lam δ R p h y i j := by
      funext y
      rfl
    rw [hew] at ht
    exact ht
  · have heu : densityPrincipalEntry (fun _ : R3 => (1 : ℝ)) r q (fun y => h y i j) =
        fun y => actualPrincipalMatrix g L lam δ R p h y i j := by
      funext y
      simp only [densityPrincipalEntry,principalEntry,one_mul,actualPrincipalMatrix,r,q]
    rw [heu] at hu
    exact hu

/-- Exact second derivative of the existing first-order scalar natural-adjoint coefficient. -/
lemma directional_second_adjointFirstCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hp : ∀ x, mu x ≠ 0)
    (i : Fin 3) (X Y x : R3) :
    directionalFDeriv Y (directionalFDeriv X
      (fun y => adjointFirstCoefficient v mu a y i)) x =
      2 * directionalFDeriv Y (directionalFDeriv X (fun y => (mu y)⁻¹)) x *
        (∑ j, directionalFDeriv (v j) (fun y => mu y*a y i j) x) +
      2 * directionalFDeriv X (fun y => (mu y)⁻¹) x *
        (∑ j, directionalFDeriv Y
          (directionalFDeriv (v j) (fun y => mu y*a y i j)) x) +
      2 * directionalFDeriv Y (fun y => (mu y)⁻¹) x *
        (∑ j, directionalFDeriv X
          (directionalFDeriv (v j) (fun y => mu y*a y i j)) x) +
      2 * (mu x)⁻¹ * (∑ j, directionalFDeriv Y (directionalFDeriv X
        (directionalFDeriv (v j) (fun y => mu y*a y i j))) x) := by
  let F : Fin 3 → R3 → ℝ := fun j y => mu y*a y i j
  let b : R3 → ℝ := fun y => ∑ j, directionalFDeriv (v j) (F j) y
  have hF (j : Fin 3) : ContDiff ℝ ∞ (F j) := hm.mul (ha i j)
  have hb : ContDiff ℝ ∞ b := ContDiff.sum
    (fun j _ => contDiff_directionalFDeriv (v j) (F j) (hF j))
  have hn : ContDiff ℝ ∞ (fun y => (mu y)⁻¹) := hm.inv hp
  have he : (fun y => adjointFirstCoefficient v mu a y i) =
      fun y => (2 * (mu y)⁻¹) * b y := by funext y; rfl
  have hfirst (V : R3) : directionalFDeriv V (fun y => 2*(mu y)⁻¹) x =
      2*directionalFDeriv V (fun y => (mu y)⁻¹) x := by
    simpa only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,
      zero_mul,zero_add] using
      directional_mul V (fun _ : R3 => (2 : ℝ)) (fun y => (mu y)⁻¹) contDiff_const hn x
  have hsecond : directionalFDeriv Y (directionalFDeriv X (fun y => 2*(mu y)⁻¹)) x =
      2*directionalFDeriv Y (directionalFDeriv X (fun y => (mu y)⁻¹)) x := by
    have he2 : directionalFDeriv X (fun y => 2*(mu y)⁻¹) =
        fun y => 2*directionalFDeriv X (fun y => (mu y)⁻¹) y := by
      funext y
      simpa only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,
        zero_mul,zero_add] using
        directional_mul X (fun _ : R3 => (2 : ℝ)) (fun y => (mu y)⁻¹) contDiff_const hn y
    rw [he2]
    simpa only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,
      zero_mul,zero_add] using
      directional_mul Y (fun _ : R3 => (2 : ℝ))
        (directionalFDeriv X (fun y => (mu y)⁻¹)) contDiff_const
        (contDiff_directionalFDeriv X _ hn) x
  have hsX := directionalFDeriv_fintype_sum X
    (fun j => directionalFDeriv (v j) (F j))
    (fun j => contDiff_directionalFDeriv (v j) (F j) (hF j)) x
  have hsY := directionalFDeriv_fintype_sum Y
    (fun j => directionalFDeriv (v j) (F j))
    (fun j => contDiff_directionalFDeriv (v j) (F j) (hF j)) x
  have hsYX := directionalFDeriv_second_fintype_sum Y X
    (fun j => directionalFDeriv (v j) (F j))
    (fun j => contDiff_directionalFDeriv (v j) (F j) (hF j)) x
  change directionalFDeriv X b x = _ at hsX
  change directionalFDeriv Y b x = _ at hsY
  change directionalFDeriv Y (directionalFDeriv X b) x = _ at hsYX
  rw [he,directional_second_mul X Y _ _ (contDiff_const.mul hn) hb x,
    hfirst X,hfirst Y,hsecond,hsX,hsY,hsYX]

lemma directional_second_adjointFirstCoefficient_bound (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hp : ∀ x, mu x ≠ 0)
    (i : Fin 3) (X Y x : R3) (M B1 B2 B3 : ℝ) (hM : 0 ≤ M)
    (hn : |(mu x)⁻¹| ≤ M)
    (hDXn : |directionalFDeriv X (fun y => (mu y)⁻¹) x| ≤ M)
    (hDYn : |directionalFDeriv Y (fun y => (mu y)⁻¹) x| ≤ M)
    (hD2n : |directionalFDeriv Y (directionalFDeriv X (fun y => (mu y)⁻¹)) x| ≤ M)
    (h1 : ∀ j, |directionalFDeriv (v j) (fun y => mu y*a y i j) x| ≤ B1)
    (h2X : ∀ j, |directionalFDeriv X
      (directionalFDeriv (v j) (fun y => mu y*a y i j)) x| ≤ B2)
    (h2Y : ∀ j, |directionalFDeriv Y
      (directionalFDeriv (v j) (fun y => mu y*a y i j)) x| ≤ B2)
    (h3 : ∀ j, |directionalFDeriv Y (directionalFDeriv X
      (directionalFDeriv (v j) (fun y => mu y*a y i j))) x| ≤ B3) :
    |directionalFDeriv Y (directionalFDeriv X
      (fun y => adjointFirstCoefficient v mu a y i)) x| ≤ 6*M*(B1+2*B2+B3) := by
  have hab (u t B : ℝ) (hu : |u| ≤ M) (ht : |t| ≤ 3*B) :
      |2*u*t| ≤ 2*M*(3*B) := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) ht
      (abs_nonneg _) (by positivity)
  rw [directional_second_adjointFirstCoefficient v mu a hm ha hp i X Y x]
  have hs1 := abs_sum_three_le _ B1 h1
  have hs2X := abs_sum_three_le _ B2 h2X
  have hs2Y := abs_sum_three_le _ B2 h2Y
  have hs3 := abs_sum_three_le _ B3 h3
  have h1' := hab _ _ B1 hD2n hs1
  have h2' := hab _ _ B2 hDXn hs2Y
  have h3' := hab _ _ B2 hDYn hs2X
  have h4' := hab _ _ B3 hn hs3
  have habs (u v w z : ℝ) : |u+v+w+z| ≤ |u|+|v|+|w|+|z| := by
    linarith [abs_add_le u v,abs_add_le (u+v) w,abs_add_le (u+v+w) z]
  exact (habs _ _ _ _).trans (by nlinarith)

lemma directional_adjointZeroCoefficient_bound (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hp : ∀ x, mu x ≠ 0)
    (X x : R3) (M B2 B3 : ℝ) (hM : 0 ≤ M)
    (hn : |(mu x)⁻¹| ≤ M)
    (hDn : |directionalFDeriv X (fun y => (mu y)⁻¹) x| ≤ M)
    (h2 : ∀ i j, |directionalFDeriv (v j) (directionalFDeriv (v i)
      (fun y => mu y*a y i j)) x| ≤ B2)
    (h3 : ∀ i j, |directionalFDeriv X (directionalFDeriv (v j) (directionalFDeriv (v i)
      (fun y => mu y*a y i j))) x| ≤ B3) :
    |directionalFDeriv X (adjointZeroCoefficient v mu a) x| ≤ 9*M*(B2+B3) := by
  rw [directional_adjointZeroCoefficient v mu a hm ha hp X x]
  have hs2 := abs_sum_three_le _ (3*B2) (fun i => abs_sum_three_le _ B2 (h2 i))
  have hs3 := abs_sum_three_le _ (3*B3) (fun i => abs_sum_three_le _ B3 (h3 i))
  have hleft : |directionalFDeriv X (fun y => (mu y)⁻¹) x *
      (∑ i, ∑ j, directionalFDeriv (v j) (directionalFDeriv (v i)
        (fun y => mu y*a y i j)) x)| ≤ M*(9*B2) := by
    rw [abs_mul]
    exact mul_le_mul hDn (by nlinarith [hs2]) (abs_nonneg _) hM
  have hright : |(mu x)⁻¹ * (∑ i, ∑ j, directionalFDeriv X
      (directionalFDeriv (v j) (directionalFDeriv (v i)
        (fun y => mu y*a y i j))) x)| ≤ M*(9*B3) := by
    rw [abs_mul]
    exact mul_le_mul hn (by nlinarith [hs3]) (abs_nonneg _) hM
  exact (abs_add_le _ _).trans (by nlinarith)

/-- Actual natural-adjoint second/zeroth derivatives have fixed eps beta bounds from literal h jets. -/
theorem exists_actual_adjoint_higher_derivatives_uniform_bounds (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ Csecond Czero : ℝ, 0 < Csecond ∧ 0 < Czero ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j, CoordinateThreeJetBound (fun y => h y i j) x
        (eps * referenceRadius δ R p L x)) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x * beta^2 ≤ eps →
      (∀ i k l,
        |directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k)
          (fun y => adjointFirstCoefficient coordinateDirection
            (fun z => referenceDensityFamily g L (lam,z))
            (actualPrincipalMatrix g L lam δ R p h) y i)) x| ≤ Csecond*eps*beta) ∧
      ∀ k, |directionalFDeriv (coordinateDirection k)
        (adjointZeroCoefficient coordinateDirection (fun z => referenceDensityFamily g L (lam,z))
          (actualPrincipalMatrix g L lam δ R p h)) x| ≤ Czero*eps*beta := by
  obtain ⟨M0,C1,C2,hM0,hC1,hC2,hweighted⟩ :=
    exists_actual_weighted_principal_uniform_bounds g hg L hL K hK
  obtain ⟨C3,hC3,hthird⟩ := exists_actual_principal_third_uniform_bounds g hg L hL K hK
  obtain ⟨M,hM,hbackground⟩ := exists_referenceBackground_uniform_three_jet_bound g hg L K hK
  refine ⟨6*M*(C1+2*C2+C3),9*M*(C2+C3),by positivity,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet beta hb hsmall
  have htwo (i j k l : Fin 3) : TwoJetBound (coordinateDirection k) (coordinateDirection l)
      (fun y => h y i j) x (eps*referenceRadius δ R p L x) :=
    coordinateThreeJetBound_twoJetBound _ _ _ (hhjet i j) k l
  obtain ⟨_,hentry⟩ :=
    hweighted lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh htwo hb hsmall
  have hentry3 := hthird lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall
  let mu : R3 → ℝ := fun y => referenceDensityFamily g L (lam,y)
  let a := actualPrincipalMatrix g L lam δ R p h
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp
    (contDiff_const.prodMk contDiff_id)
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (fun y => a y i j) :=
    contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  have hpos : ∀ y, mu y ≠ 0 := fun y => ne_of_gt (referenceDensityFamily_pos g hg L (lam,y))
  have hnjet : CoordinateThreeJetBound (fun y => (mu y)⁻¹) x M := by
    simpa [mu,referenceBackgroundFamily] using hbackground lam hlam x hx (.inl 1)
  have hscale (C : ℝ) (hC : 0 ≤ C) : C*eps ≤ C*eps*beta := by
    nlinarith [mul_nonneg (show 0 ≤ C*eps by positivity) (sub_nonneg.mpr hb)]
  have h1 (i j : Fin 3) : |directionalFDeriv (coordinateDirection j)
      (fun y => mu y*a y i j) x| ≤ C1*eps*beta :=
    (hentry i j j j).1.trans ((div_le_self_of_one_le _ _ (by positivity) hb).trans (hscale C1 hC1.le))
  have h2 (i j k l : Fin 3) : |directionalFDeriv (coordinateDirection l)
      (directionalFDeriv (coordinateDirection k) (fun y => mu y*a y i j)) x| ≤ C2*eps*beta :=
    (hentry i j k l).2.trans (hscale C2 hC2.le)
  have h3 (i j k l m : Fin 3) : |directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection l)
        (directionalFDeriv (coordinateDirection k) (fun y => mu y*a y i j))) x| ≤ C3*eps*beta :=
    (hentry3 i j k l m).1
  constructor
  · intro i k l
    have ht := directional_second_adjointFirstCoefficient_bound coordinateDirection mu a hm ha hpos i
      (coordinateDirection k) (coordinateDirection l) x M (C1*eps*beta) (C2*eps*beta) (C3*eps*beta)
      (by linarith) hnjet.1 (hnjet.2.1 k) (hnjet.2.1 l) (hnjet.2.2.1 k l)
      (h1 i) (fun j => h2 i j j k) (fun j => h2 i j j l) (fun j => h3 i j j k l)
    convert ht using 1 <;> ring
  · intro k
    have ht := directional_adjointZeroCoefficient_bound coordinateDirection mu a hm ha hpos
      (coordinateDirection k) x M (C2*eps*beta) (C3*eps*beta)
      (by linarith) hnjet.1 (hnjet.2.1 k)
      (fun i j => h2 i j i j) (fun i j => h3 i j i j k)
    convert ht using 1 <;> ring

end OAI.AnisotropicCalderon.ActualPrincipalAdjointHigherJets
