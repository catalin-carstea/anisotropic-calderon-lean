import Calderon.AngularBaseIntegration

noncomputable section
namespace OAI.AnisotropicCalderon.AngularPolynomial
open MeasureTheory
open scoped BigOperators

theorem compact_base_weighted_coercive_lower_bound (k t : ℝ) (hk : 0 ≤ k)
    (u a : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport u) (ha' : ∀ x, u x ≠ 0 → deriv a x ≤ -t) :
    (∫ x : ℝ, deriv u x ^ 2) + k ^ 2 * (∫ x : ℝ, a x ^ 2 * u x ^ 2) +
      k * t * (∫ x : ℝ, u x ^ 2) ≤
        ∫ x : ℝ, weightedBaseDerivativePlus k a u x ^ 2 := by
  have hs : HasCompactSupport (fun x : ℝ => u x ^ 2) := by
    simpa only [pow_two] using
      (show HasCompactSupport (fun x : ℝ => u x * u x) from hc.mul_right)
  have hi : Integrable (fun x : ℝ => deriv a x * u x ^ 2) :=
    ((ha.continuous_deriv (by norm_num)).mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport hs.mul_left
  have hj := (compact_base_square_integrable u hu.continuous hc).const_mul (-t)
  have hp : ∀ x : ℝ, deriv a x * u x ^ 2 ≤ -t * u x ^ 2 := by
    intro x
    by_cases hx : u x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_right (ha' x hx) (sq_nonneg _)
  have hle := integral_mono hi hj hp
  rw [integral_const_mul] at hle
  have hmul := mul_le_mul_of_nonneg_left hle hk
  rw [compact_base_weighted_square_expansion k u a hu ha hc]
  nlinarith

def finiteWeightedSquare {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (u : ι → ℝ → ℝ) (x : ℝ) : ℝ := ∑ i ∈ s, w i * u i x ^ 2

lemma finiteWeightedSquare_integrable {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (u : ι → ℝ → ℝ) (hu : ∀ i ∈ s, Continuous (u i))
    (hc : ∀ i ∈ s, HasCompactSupport (u i)) :
    Integrable (finiteWeightedSquare s w u) := by
  classical
  exact integrable_finsetSum s fun i hi =>
    (compact_base_square_integrable (u i) (hu i hi) (hc i hi)).const_mul (w i)

lemma integral_finiteWeightedSquare {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (u : ι → ℝ → ℝ) (hu : ∀ i ∈ s, Continuous (u i))
    (hc : ∀ i ∈ s, HasCompactSupport (u i)) :
    (∫ x : ℝ, finiteWeightedSquare s w u x) =
      ∑ i ∈ s, w i * (∫ x : ℝ, u i x ^ 2) := by
  classical
  change (∫ x : ℝ, ∑ i ∈ s, w i * u i x ^ 2) = _
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro i hi
    exact (compact_base_square_integrable (u i) (hu i hi) (hc i hi)).const_mul (w i)

theorem compact_finite_weighted_coercive_lower_bound {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (k t : ℝ) (hk : 0 ≤ k) (u : ι → ℝ → ℝ) (a : ℝ → ℝ)
    (hu : ∀ i ∈ s, ContDiff ℝ 1 (u i)) (ha : ContDiff ℝ 1 a)
    (hc : ∀ i ∈ s, HasCompactSupport (u i))
    (ha' : ∀ i ∈ s, ∀ x, u i x ≠ 0 → deriv a x ≤ -t) :
    (∫ x : ℝ, finiteWeightedSquare s w (fun i => deriv (u i)) x) +
      k ^ 2 * (∫ x : ℝ, finiteWeightedSquare s w (fun i x => a x * u i x) x) +
      k * t * (∫ x : ℝ, finiteWeightedSquare s w u x) ≤
        ∫ x : ℝ, finiteWeightedSquare s w
          (fun i => weightedBaseDerivativePlus k a (u i)) x := by
  classical
  rw [integral_finiteWeightedSquare s w (fun i => deriv (u i))
      (fun i hi => (hu i hi).continuous_deriv (by norm_num)) (fun i hi => (hc i hi).deriv),
    integral_finiteWeightedSquare s w (fun i x => a x * u i x)
      (fun i hi => ha.continuous.mul (hu i hi).continuous) (fun i hi => (hc i hi).mul_left),
    integral_finiteWeightedSquare s w u (fun i hi => (hu i hi).continuous) hc,
    integral_finiteWeightedSquare s w (fun i => weightedBaseDerivativePlus k a (u i))
      (fun i hi => (hu i hi).continuous_deriv (by norm_num) |>.add
        ((continuous_const.mul ha.continuous).mul (hu i hi).continuous))
      (fun i hi => (hc i hi).deriv.add (show HasCompactSupport
        (fun x => k * a x * u i x) from (hc i hi).mul_left))]
  simp_rw [mul_pow]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left
    (compact_base_weighted_coercive_lower_bound k t hk (u i) a (hu i hi) ha
      (hc i hi) (ha' i hi)) (hw i hi)
  convert h using 1 <;> ring

def finiteCoefficientPolynomial {σ : Type*} (s : Finset (σ →₀ ℕ))
    (u : (σ →₀ ℕ) → ℝ → ℝ) (x : ℝ) : MvPolynomial σ ℝ :=
  ∑ α ∈ s, MvPolynomial.monomial α (u α x)

lemma coeff_finiteCoefficientPolynomial {σ : Type*} (s : Finset (σ →₀ ℕ))
    (u : (σ →₀ ℕ) → ℝ → ℝ) (x : ℝ) (α : σ →₀ ℕ) (hα : α ∈ s) :
    (finiteCoefficientPolynomial s u x).coeff α = u α x := by
  classical
  simp [finiteCoefficientPolynomial, MvPolynomial.coeff_monomial, hα]

lemma coeff_finiteCoefficientPolynomial_of_notMem {σ : Type*} (s : Finset (σ →₀ ℕ))
    (u : (σ →₀ ℕ) → ℝ → ℝ) (x : ℝ) (α : σ →₀ ℕ) (hα : α ∉ s) :
    (finiteCoefficientPolynomial s u x).coeff α = 0 := by
  classical
  simp [finiteCoefficientPolynomial, MvPolynomial.coeff_monomial, hα]

lemma fischerInner_finset_sum_left {σ ι : Type*} [Fintype σ]
    (s : Finset ι) (p : ι → MvPolynomial σ ℝ) (q : MvPolynomial σ ℝ) :
    fischerInner (∑ i ∈ s, p i) q = ∑ i ∈ s, fischerInner (p i) q := by
  rw [fischerInner_symm, fischerInner_sum_right]
  apply Finset.sum_congr rfl
  intro i hi
  exact fischerInner_symm _ _

lemma fischerInner_finiteCoefficientPolynomial {σ : Type*} [Fintype σ]
    (s : Finset (σ →₀ ℕ)) (u : (σ →₀ ℕ) → ℝ → ℝ) (x : ℝ) :
    fischerInner (finiteCoefficientPolynomial s u x) (finiteCoefficientPolynomial s u x) =
      finiteWeightedSquare s fischerWeight u x := by
  classical
  have hsum := fischerInner_finset_sum_left s
    (fun α => MvPolynomial.monomial α (u α x)) (finiteCoefficientPolynomial s u x)
  change fischerInner (∑ α ∈ s, MvPolynomial.monomial α (u α x))
    (finiteCoefficientPolynomial s u x) = finiteWeightedSquare s fischerWeight u x
  rw [hsum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [fischerInner_monomial_left, coeff_finiteCoefficientPolynomial s u x α hα]
  ring

lemma fischerInner_finiteCoefficientPolynomial_integrable {σ : Type*} [Fintype σ]
    (s : Finset (σ →₀ ℕ)) (u : (σ →₀ ℕ) → ℝ → ℝ)
    (hu : ∀ α ∈ s, Continuous (u α)) (hc : ∀ α ∈ s, HasCompactSupport (u α)) :
    Integrable (fun x : ℝ =>
      fischerInner (finiteCoefficientPolynomial s u x) (finiteCoefficientPolynomial s u x)) := by
  simpa only [fischerInner_finiteCoefficientPolynomial] using
    finiteWeightedSquare_integrable s fischerWeight u hu hc

theorem compact_fischer_base_coercive_lower_bound {σ : Type*} [Fintype σ]
    (s : Finset (σ →₀ ℕ)) (k t : ℝ) (hk : 0 ≤ k)
    (u : (σ →₀ ℕ) → ℝ → ℝ) (a : ℝ → ℝ)
    (hu : ∀ α ∈ s, ContDiff ℝ 1 (u α)) (ha : ContDiff ℝ 1 a)
    (hc : ∀ α ∈ s, HasCompactSupport (u α))
    (ha' : ∀ α ∈ s, ∀ x, u α x ≠ 0 → deriv a x ≤ -t) :
    (∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s (fun α => deriv (u α)) x)
      (finiteCoefficientPolynomial s (fun α => deriv (u α)) x)) +
    k ^ 2 * (∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s (fun α x => a x * u α x) x)
      (finiteCoefficientPolynomial s (fun α x => a x * u α x) x)) +
    k * t * (∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s u x) (finiteCoefficientPolynomial s u x)) ≤
    ∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s (fun α => weightedBaseDerivativePlus k a (u α)) x)
      (finiteCoefficientPolynomial s (fun α => weightedBaseDerivativePlus k a (u α)) x) := by
  simp_rw [fischerInner_finiteCoefficientPolynomial]
  exact compact_finite_weighted_coercive_lower_bound s fischerWeight
    (fun α hα => (fischerWeight_pos α).le) k t hk u a hu ha hc ha'

lemma deriv_coeff_finiteCoefficientPolynomial {σ : Type*}
    (s : Finset (σ →₀ ℕ)) (u : (σ →₀ ℕ) → ℝ → ℝ) (α : σ →₀ ℕ) (hα : α ∈ s)
    (x : ℝ) :
    deriv (fun y : ℝ => (finiteCoefficientPolynomial s u y).coeff α) x = deriv (u α) x := by
  have heq : (fun y : ℝ => (finiteCoefficientPolynomial s u y).coeff α) = u α :=
    funext fun y => coeff_finiteCoefficientPolynomial s u y α hα
  rw [heq]

lemma integral_finite_profile_square {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (b : ℝ → ℝ) (u : ι → ℝ → ℝ) (hb : Continuous b)
    (hu : ∀ i ∈ s, Continuous (u i)) (hc : ∀ i ∈ s, HasCompactSupport (u i)) :
    (∫ x : ℝ, b x * finiteWeightedSquare s w u x) =
      ∑ i ∈ s, w i * (∫ x : ℝ, b x * u i x ^ 2) := by
  classical
  have hf : ∀ i ∈ s, Integrable (fun x : ℝ => b x * u i x ^ 2) := by
    intro i hi
    have hs : HasCompactSupport (fun x : ℝ => u i x ^ 2) := by
      simpa only [pow_two] using
        (show HasCompactSupport (fun x : ℝ => u i x * u i x) from (hc i hi).mul_right)
    exact (hb.mul ((hu i hi).pow 2)).integrable_of_hasCompactSupport hs.mul_left
  have heq : (fun x : ℝ => b x * finiteWeightedSquare s w u x) =
      fun x => ∑ i ∈ s, w i * (b x * u i x ^ 2) := by
    funext x
    simp only [finiteWeightedSquare, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_finsetSum s (fun i hi => (hf i hi).const_mul (w i))]
  simp_rw [integral_const_mul]

theorem compact_finite_weighted_square_difference {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (k : ℝ) (u : ι → ℝ → ℝ) (a : ℝ → ℝ)
    (hu : ∀ i ∈ s, ContDiff ℝ 1 (u i)) (ha : ContDiff ℝ 1 a)
    (hc : ∀ i ∈ s, HasCompactSupport (u i)) :
    (∫ x : ℝ, finiteWeightedSquare s w (fun i => weightedBaseDerivativeMinus k a (u i)) x) =
      (∫ x : ℝ, finiteWeightedSquare s w (fun i => weightedBaseDerivativePlus k a (u i)) x) +
        2 * k * (∫ x : ℝ, deriv a x * finiteWeightedSquare s w u x) := by
  classical
  rw [integral_finiteWeightedSquare s w (fun i => weightedBaseDerivativeMinus k a (u i))
      (fun i hi => ((hu i hi).continuous_deriv (by norm_num)).neg.add
        ((continuous_const.mul ha.continuous).mul (hu i hi).continuous))
      (fun i hi => (hc i hi).deriv.neg.add (show HasCompactSupport
        (fun x => k * a x * u i x) from (hc i hi).mul_left)),
    integral_finiteWeightedSquare s w (fun i => weightedBaseDerivativePlus k a (u i))
      (fun i hi => ((hu i hi).continuous_deriv (by norm_num)).add
        ((continuous_const.mul ha.continuous).mul (hu i hi).continuous))
      (fun i hi => (hc i hi).deriv.add (show HasCompactSupport
        (fun x => k * a x * u i x) from (hc i hi).mul_left)),
    integral_finite_profile_square s w (deriv a) u (ha.continuous_deriv (by norm_num))
      (fun i hi => (hu i hi).continuous) hc,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [compact_base_weighted_square_difference k (u i) a (hu i hi) ha (hc i hi)]
  ring

theorem compact_finite_weighted_square_expansion {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (k : ℝ) (u : ι → ℝ → ℝ) (a : ℝ → ℝ)
    (hu : ∀ i ∈ s, ContDiff ℝ 1 (u i)) (ha : ContDiff ℝ 1 a)
    (hc : ∀ i ∈ s, HasCompactSupport (u i)) :
    (∫ x : ℝ, finiteWeightedSquare s w (fun i => weightedBaseDerivativePlus k a (u i)) x) =
      (∫ x : ℝ, finiteWeightedSquare s w (fun i => deriv (u i)) x) +
        k ^ 2 * (∫ x : ℝ, a x ^ 2 * finiteWeightedSquare s w u x) -
        k * (∫ x : ℝ, deriv a x * finiteWeightedSquare s w u x) := by
  classical
  rw [integral_finiteWeightedSquare s w (fun i => weightedBaseDerivativePlus k a (u i))
      (fun i hi => ((hu i hi).continuous_deriv (by norm_num)).add
        ((continuous_const.mul ha.continuous).mul (hu i hi).continuous))
      (fun i hi => (hc i hi).deriv.add (show HasCompactSupport
        (fun x => k * a x * u i x) from (hc i hi).mul_left)),
    integral_finiteWeightedSquare s w (fun i => deriv (u i))
      (fun i hi => (hu i hi).continuous_deriv (by norm_num)) (fun i hi => (hc i hi).deriv),
    integral_finite_profile_square s w (fun x => a x ^ 2) u (ha.continuous.pow 2)
      (fun i hi => (hu i hi).continuous) hc,
    integral_finite_profile_square s w (deriv a) u (ha.continuous_deriv (by norm_num))
      (fun i hi => (hu i hi).continuous) hc,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [compact_base_weighted_square_expansion k (u i) a (hu i hi) ha (hc i hi)]
  ring

theorem compact_fischer_base_square_difference {σ : Type*} [Fintype σ]
    (s : Finset (σ →₀ ℕ)) (k : ℝ) (u : (σ →₀ ℕ) → ℝ → ℝ) (a : ℝ → ℝ)
    (hu : ∀ α ∈ s, ContDiff ℝ 1 (u α)) (ha : ContDiff ℝ 1 a)
    (hc : ∀ α ∈ s, HasCompactSupport (u α)) :
    (∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s (fun α => weightedBaseDerivativeMinus k a (u α)) x)
      (finiteCoefficientPolynomial s (fun α => weightedBaseDerivativeMinus k a (u α)) x)) =
    (∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s (fun α => weightedBaseDerivativePlus k a (u α)) x)
      (finiteCoefficientPolynomial s (fun α => weightedBaseDerivativePlus k a (u α)) x)) +
    2 * k * (∫ x : ℝ, deriv a x * fischerInner
      (finiteCoefficientPolynomial s u x) (finiteCoefficientPolynomial s u x)) := by
  simp_rw [fischerInner_finiteCoefficientPolynomial]
  exact compact_finite_weighted_square_difference s fischerWeight k u a hu ha hc

theorem compact_fischer_base_square_expansion {σ : Type*} [Fintype σ]
    (s : Finset (σ →₀ ℕ)) (k : ℝ) (u : (σ →₀ ℕ) → ℝ → ℝ) (a : ℝ → ℝ)
    (hu : ∀ α ∈ s, ContDiff ℝ 1 (u α)) (ha : ContDiff ℝ 1 a)
    (hc : ∀ α ∈ s, HasCompactSupport (u α)) :
    (∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s (fun α => weightedBaseDerivativePlus k a (u α)) x)
      (finiteCoefficientPolynomial s (fun α => weightedBaseDerivativePlus k a (u α)) x)) =
    (∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s (fun α => deriv (u α)) x)
      (finiteCoefficientPolynomial s (fun α => deriv (u α)) x)) +
    k ^ 2 * (∫ x : ℝ, a x ^ 2 * fischerInner
      (finiteCoefficientPolynomial s u x) (finiteCoefficientPolynomial s u x)) -
    k * (∫ x : ℝ, deriv a x * fischerInner
      (finiteCoefficientPolynomial s u x) (finiteCoefficientPolynomial s u x)) := by
  simp_rw [fischerInner_finiteCoefficientPolynomial]
  exact compact_finite_weighted_square_expansion s fischerWeight k u a hu ha hc

theorem compact_base_variable_profile_lower_bound (k c : ℝ) (hk : 0 ≤ k)
    (u a beta : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a)
    (hbeta : Continuous beta) (hc : HasCompactSupport u)
    (ha' : ∀ x, u x ≠ 0 → deriv a x ≤ -c * beta x) :
    (∫ x : ℝ, deriv u x ^ 2) + k ^ 2 * (∫ x : ℝ, a x ^ 2 * u x ^ 2) +
      k * c * (∫ x : ℝ, beta x * u x ^ 2) ≤
        ∫ x : ℝ, weightedBaseDerivativePlus k a u x ^ 2 := by
  have hs : HasCompactSupport (fun x : ℝ => u x ^ 2) := by
    simpa only [pow_two] using
      (show HasCompactSupport (fun x : ℝ => u x * u x) from hc.mul_right)
  have hi : Integrable (fun x : ℝ => deriv a x * u x ^ 2) :=
    ((ha.continuous_deriv (by norm_num)).mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport hs.mul_left
  have hmass : Integrable (fun x : ℝ => beta x * u x ^ 2) :=
    (hbeta.mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport hs.mul_left
  have hj := hmass.const_mul (-c)
  have hp : ∀ x : ℝ, deriv a x * u x ^ 2 ≤ -c * (beta x * u x ^ 2) := by
    intro x
    by_cases hx : u x = 0
    · simp [hx]
    · have h := mul_le_mul_of_nonneg_right (ha' x hx) (sq_nonneg (u x))
      nlinarith only [h]
  have hle := integral_mono hi hj hp
  rw [integral_const_mul] at hle
  have hmul := mul_le_mul_of_nonneg_left hle hk
  rw [compact_base_weighted_square_expansion k u a hu ha hc]
  nlinarith only [hmul]

theorem compact_finite_variable_profile_lower_bound {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (k c : ℝ) (hk : 0 ≤ k) (u : ι → ℝ → ℝ) (a beta : ℝ → ℝ)
    (hu : ∀ i ∈ s, ContDiff ℝ 1 (u i)) (ha : ContDiff ℝ 1 a)
    (hbeta : Continuous beta) (hc : ∀ i ∈ s, HasCompactSupport (u i))
    (ha' : ∀ i ∈ s, ∀ x, u i x ≠ 0 → deriv a x ≤ -c * beta x) :
    (∫ x : ℝ, finiteWeightedSquare s w (fun i => deriv (u i)) x) +
      k ^ 2 * (∫ x : ℝ, finiteWeightedSquare s w (fun i x => a x * u i x) x) +
      k * c * (∫ x : ℝ, beta x * finiteWeightedSquare s w u x) ≤
        ∫ x : ℝ, finiteWeightedSquare s w
          (fun i => weightedBaseDerivativePlus k a (u i)) x := by
  classical
  rw [integral_finiteWeightedSquare s w (fun i => deriv (u i))
      (fun i hi => (hu i hi).continuous_deriv (by norm_num)) (fun i hi => (hc i hi).deriv),
    integral_finiteWeightedSquare s w (fun i x => a x * u i x)
      (fun i hi => ha.continuous.mul (hu i hi).continuous) (fun i hi => (hc i hi).mul_left),
    integral_finite_profile_square s w beta u hbeta (fun i hi => (hu i hi).continuous) hc,
    integral_finiteWeightedSquare s w (fun i => weightedBaseDerivativePlus k a (u i))
      (fun i hi => ((hu i hi).continuous_deriv (by norm_num)).add
        ((continuous_const.mul ha.continuous).mul (hu i hi).continuous))
      (fun i hi => (hc i hi).deriv.add (show HasCompactSupport
        (fun x => k * a x * u i x) from (hc i hi).mul_left))]
  simp_rw [mul_pow]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left
    (compact_base_variable_profile_lower_bound k c hk (u i) a beta (hu i hi) ha hbeta
      (hc i hi) (ha' i hi)) (hw i hi)
  convert h using 1 <;> ring

theorem compact_fischer_variable_profile_lower_bound {σ : Type*} [Fintype σ]
    (s : Finset (σ →₀ ℕ)) (k c : ℝ) (hk : 0 ≤ k)
    (u : (σ →₀ ℕ) → ℝ → ℝ) (a beta : ℝ → ℝ)
    (hu : ∀ α ∈ s, ContDiff ℝ 1 (u α)) (ha : ContDiff ℝ 1 a)
    (hbeta : Continuous beta) (hc : ∀ α ∈ s, HasCompactSupport (u α))
    (ha' : ∀ α ∈ s, ∀ x, u α x ≠ 0 → deriv a x ≤ -c * beta x) :
    (∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s (fun α => deriv (u α)) x)
      (finiteCoefficientPolynomial s (fun α => deriv (u α)) x)) +
    k ^ 2 * (∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s (fun α x => a x * u α x) x)
      (finiteCoefficientPolynomial s (fun α x => a x * u α x) x)) +
    k * c * (∫ x : ℝ, beta x * fischerInner
      (finiteCoefficientPolynomial s u x) (finiteCoefficientPolynomial s u x)) ≤
    ∫ x : ℝ, fischerInner
      (finiteCoefficientPolynomial s (fun α => weightedBaseDerivativePlus k a (u α)) x)
      (finiteCoefficientPolynomial s (fun α => weightedBaseDerivativePlus k a (u α)) x) := by
  simp_rw [fischerInner_finiteCoefficientPolynomial]
  exact compact_finite_variable_profile_lower_bound s fischerWeight
    (fun α hα => (fischerWeight_pos α).le) k c hk u a beta hu ha hbeta hc ha'

end OAI.AnisotropicCalderon.AngularPolynomial
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_base_weighted_coercive_lower_bound
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_finite_weighted_coercive_lower_bound
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.fischerInner_finiteCoefficientPolynomial
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_fischer_base_coercive_lower_bound
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_fischer_base_square_difference
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_fischer_base_square_expansion
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.deriv_coeff_finiteCoefficientPolynomial
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_base_variable_profile_lower_bound
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_finite_variable_profile_lower_bound
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_fischer_variable_profile_lower_bound
