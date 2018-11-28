abstract type Formula end
abstract type Compound <: Formula end
abstract type Unit <: Formula end
abstract type Literal <: Unit end

struct True <: Literal end
struct False <: Literal end

struct Atom <: Unit
	p::String
end

struct Neg <: Unit
	ϕ::Formula
end

struct And <: Compound
	ϕ₁::Formula
	ϕ₂::Formula
end

struct Or <: Compound
	ϕ₁::Formula
	ϕ₂::Formula
end

struct Imp <: Compound
	ϕ₁::Formula
	ϕ₂::Formula
end

function Base.show(io::IO, ϕ::Unit)
	if typeof(ϕ) == Neg
		if typeof(ϕ.ϕ) <: Unit
			print(io, '¬', ϕ.ϕ)
		else
			print(io, "¬(", ϕ.ϕ, ')')
		end
	else
		print(io, ϕ.p)
	end
end

function Base.show(io::IO, ϕ::Compound)
	if typeof(ϕ.ϕ₁) <: Unit
		print(io, ϕ.ϕ₁)
	else
		print(io, '(', ϕ.ϕ₁, ')')
	end

	if typeof(ϕ) == And
		print(io, " & ")
	elseif typeof(ϕ) == Or
		print(io, " | ")
	else
		print(io, " → ")
	end

	if typeof(ϕ.ϕ₂) <: Unit
		print(io, ϕ.ϕ₂)
	else
		print(io, '(', ϕ.ϕ₂, ')')
	end
end

struct Sequent
	Φ::Array{Formula}
	ψ::Formula
end

¬ϕ = Neg(ϕ)
ϕ ∧ ψ = And(ϕ, ψ)
ϕ ∨ ψ = Or(ϕ, ψ)
ϕ → ψ = Imp(ϕ, ψ)

@enum Assoc LeftAssoc RightAssoc

PARENS = ["()", "[]"]
TRUE = ["T", "TRUE"]
FALSE = ["F", "FALSE"]
ATOM = r"^[a-z][0-9]*$"
NEG = ["!"]
AND = ["&", "*"]
OR  = ["|", "+"]
IMP = ["->"]
SEQ = ["=>"]

function balanced_parens(ϕ, parens)
	c = 0
	for x ∈ ϕ
		if x == parens[1]
			c += 1
		elseif x == parens[2]
			c -= 1
			if c < 0
				return false
			end
		end
	end
	return c == 0
end

balanced_parens(ϕ) = all(balanced_parens(ϕ, parens) for parens ∈ PARENS)

function parse_unary(ϕ, Op, OP)
	for op ∈ OP
		if startswith(ϕ, op)
			return Op(parse_formula(ϕ[length(op)+1:end]))
		end
	end
end

function parse_binary(ϕ, Op, OP, assoc)
	for op ∈ OP
		splits = split(ϕ, op)
		e_range = (assoc == LeftAssoc ? reverse : identity)(1:length(splits)-1)
		for e ∈ e_range
			ϕ₁ = join(splits[1:e], op)
			ϕ₂ = join(splits[e+1:end], op)
			if balanced_parens(ϕ₁) && balanced_parens(ϕ₂)
				return Op(parse_formula(ϕ₁), parse_formula(ϕ₂))
			end
		end
	end
end

is_literal(ϕ) = ϕ ∈ TRUE || ϕ ∈ FALSE
is_atomic(ϕ) = match(ATOM, ϕ) ≠ nothing
parse_neg(ϕ) = parse_unary(ϕ, Neg, NEG)
parse_and(ϕ) = parse_binary(ϕ, And, AND, LeftAssoc)
parse_or(ϕ)  = parse_binary(ϕ, Or, OR, LeftAssoc)
parse_imp(ϕ) = parse_binary(ϕ, Imp, IMP, RightAssoc)

function converge(subject, functions)
	while true
		subject_old = subject
		for f ∈ functions
			subject = f(subject)
		end
		if subject_old == subject
			return subject
		end
	end
end

strip_parens(ϕ, parens) = !isempty(ϕ) && ϕ[[1, end]] == parens ? ϕ[2:end-1] : ϕ
strip_parens(ϕ) = converge(ϕ, [ϕ -> strip_parens(ϕ, parens) for parens ∈ PARENS])
strip_formula(ϕ) = converge(ϕ, [strip, strip_parens])

function input(prompt="")
	print(prompt)
	return chomp(readline())
end

function continue_abort()
	while true
		inp = input("[C]ontinue/[A]bort? ")
		if inp == "c" || inp == "C"
			break
		elseif inp == "a" || inp == "A"
			println("Aborting")
			exit()
		end
	end
end

function parse_formula(ϕ::Formula)
	return ϕ
end

function parse_formula(ϕ::AbstractString)
	ϕ = strip_formula(ϕ)
	for p in [parse_imp, parse_or, parse_and, parse_neg]
		if (ϕ⁺ = p(ϕ)) ≠ nothing
			return ϕ⁺
		end
	end
	if is_literal(ϕ)
		return ϕ ∈ TRUE ? True() : False()
	end
	if !is_atomic(ϕ)
		println("Following will be regarded as an atomic proposition: >$ϕ<")
		continue_abort()
	end
	return Atom(ϕ)
end

function parse_sequent(Δ)
	Φ = ""
	ψ = Δ
	for seq ∈ SEQ
		splits = split(Δ, seq)
		if length(splits) == 2
			Φ, ψ = splits
			break
		end
		if length(splits) > 2
			println("Multiple $seq symbols detected")
			continue_abort()
		end
	end
	Φ = map(parse_formula, split(Φ, ',', keepempty=false))
	ψ = parse_formula(ψ)
	Sequent(Φ, ψ)
end

struct ProofStep
	indent::Bool
	ϕ::Formula
	rationale::String
	outdent::Bool
end

ProofStep(ϕ::Formula, rationale::AbstractString) = ProofStep(false, ϕ, rationale, false)
ProofStep(indent::Bool, ϕ::Formula, rationale::AbstractString) = ProofStep(indent, ϕ, rationale, false)
ProofStep(ϕ::Formula, rationale::AbstractString, outdent::Bool) = ProofStep(false, ϕ, rationale, outdent)

(Γ::Array{ProofStep})(i::Int64) = Γ[i].ϕ

function accessible(Γ::Array{ProofStep}, ante::Int, subseq::Int)
	if ante < subseq ≤ length(Γ) + 1 && !Γ[ante].outdent
		d = 0
		for i ∈ ante+1:subseq-1
			d += Γ[i].indent - Γ[i].outdent
			if d < 0
				return
			end
		end
		return d
	end
end

Γ::Array{ProofStep} ≡ ante::Int =
	accessible(Γ, ante, length(Γ) + 1) ≠ nothing

is_subproof(Γ::Array{ProofStep}, ante::Int, subseq::Int) =
	Γ[ante].indent && Γ[subseq].outdent && accessible(Γ, ante, subseq) == 0

function andi(Γ, i, j)
	if Γ ≡ i && Γ ≡ j
		ProofStep(Γ(i) ∧ Γ(j), "∧ᵢ, $i, $j")
	end
end

function ande1(Γ, i)
	if Γ ≡ i
		ϕ = Γ(i)
		if typeof(ϕ) == And
			ProofStep(ϕ.ϕ₁, "∧ₑ₁, $i")
		end
	end
end

function ande2(Γ, i)
	if Γ ≡ i
		ϕ = Γ(i)
		if typeof(ϕ) == And
			ProofStep(ϕ.ϕ₂, "∧ₑ₂, $i")
		end
	end
end

function ori1(Γ, i, ψ)
	if Γ ≡ i
		ψ = parse_formula(ψ)
		ProofStep(Γ(i) ∨ ψ, "∨ᵢ₁, $i")
	end
end

function ori2(Γ, i, ψ)
	if Γ ≡ i
		ψ = parse_formula(ψ)
		ProofStep(ψ ∨ Γ(i), "∨ᵢ₂, $i")
	end
end

function ore(Γ, i, J, K)
	j₁, j₂ = J
	k₁, k₂ = K
	if Γ ≡ i && Γ ≡ j₂ && Γ ≡ k₂ && is_subproof(Γ, J...) && is_subproof(Γ, K...)
		χ₁ = Γ(j₂)
		χ₂ = Γ(k₂)
		if typeof(Γ(i)) == Or && χ₁ == χ₂
			ProofStep(χ₁, "∨ₑ, $i, $j₁-$j₂, $k₁-$k₂")
		end
	end
end

function impi(Γ, I)
	i₁, i₂ = I
	if Γ ≡ i₂ && is_subproof(Γ, I...)
		ProofStep(Γ(i₁) → Γ(i₂), "→ᵢ, $i₁-$i₂")
	end
end

function impe(Γ, i, j)
	if Γ ≡ i && Γ ≡ j
		ϕ = Γ(j)
		if typeof(ϕ) == Imp && Γ(i) == ϕ.ϕ₁
			ProofStep(ϕ.ϕ₂, "→ₑ, $i, $j")
		end
	end
end

function negi(Γ, I)
	i₁, i₂ = I
	if Γ ≡ i₂ && is_subproof(Γ, I...) && Γ(i₂) == False()
		ProofStep(¬Γ(i₁), "¬ᵢ, $i₁-$i₂")
	end
end

function nege(Γ, i, j)
	if Γ ≡ i && Γ ≡ j
		ϕ₁ = Γ(i)
		ϕ₂ = Γ(j)
		if typeof(ϕ₂) == Neg && ϕ₁ == ϕ₂.ϕ
			ProofStep(False(), "¬ₑ, $i, $j")
		end
	end
end

function bote(Γ, i, ψ)
	if Γ ≡ i && Γ(i) == False()
		ψ = parse_formula(ψ)
		ProofStep(ψ, "⊥ₑ, $i")
	end
end

function negnegi(Γ, i)
	if Γ ≡ i
		ProofStep(¬¬Γ(i), "¬¬ᵢ, $i")
	end
end

function negnege(Γ, i)
	if Γ ≡ i
		ϕ = Γ(i)
		if typeof(ϕ) == Neg
			ϕ = ϕ.ϕ
			if typeof(ϕ) == Neg
				ProofStep(ϕ.ϕ, "¬¬ₑ, $i")
			end
		end
	end
end

function MT(Γ, i, j)
	if Γ ≡ i && Γ ≡ j
		ϕ₁ = Γ(i)
		ϕ₂ = Γ(j)
		if typeof(ϕ₁) == Imp && typeof(ϕ₂) == Neg && ϕ₁.ϕ₂ == ϕ₂.ϕ
			ProofStep(¬ϕ₁.ϕ₁, "MT, $i, $j")
		end
	end
end

function PBC(Γ, I)
	i₁, i₂ = I
	if Γ ≡ i₂ && is_subproof(Γ, I...) && Γ(i₂) == False()
		ϕ = Γ(i₁)
		if typeof(ϕ) == Neg
			ProofStep(ϕ.ϕ, "PBC, $i₁, $i₂")
		end
	end
end

function LEM(Γ, ψ)
	ψ = parse_formula(ψ)
	ProofStep(ψ ∨ ¬ψ, "LEM")
end

function assume(Γ, ψ)
	ψ = parse_formula(ψ)
	ProofStep(true, ψ, "Assumption")
end

nd_rules = String.(Symbol.((andi, ande1, ande2,
							ori1, ori2, ore,
							impi, impe,
							negi, nege,
							bote,
							negnegi, negnege,
							MT, PBC, LEM,
							assume)))

isnumstr(str) = all(isdigit(x) for x in str)

function prompt_nd()
	inp = input("Natural deduction: ")
	rule, args = map(strip, split(inp, r",|\s+", keepempty=false, limit=2))
	
	if rule ∉ nd_rules
		println("Unknown rule >", rule, "<, please retry")
		return prompt_nd()
	end

	eachmatch(r"(?:\d+-\d+)|\d+|[^\d,]+", args) # TODO

	return eval(Symbol(rule)), map(x -> parse(Int, x), args)
end

function Base.show(io::IO, γ::ProofStep)
	print(io, γ.ϕ, "\t(", γ.rationale, ")")
end

function Base.show(io::IO, Γ::Array{ProofStep})
	for (i, γ) ∈ enumerate(Γ)
		println(i, ". ", γ)
	end
end

function print_title()
	println("==== Interactive Propositional Logic Engine using Natural Deduction ====\n")
end

function clear(entirely=false)
	# println("\33[2J")
	run(`cmd /c cls`)
	if !entirely
		print_title()
	end
end

function main(args)
	clear()
	Δ = parse_sequent(input("Sequent: "))

	Γ = ProofStep[ProofStep(false, ϕ, "Premise", false) for ϕ ∈ Δ.Φ]
	while true
		clear()
		println("== Working Proof ==")
		println(Γ)
		println("== Target ==")
		println(Δ.ψ, '\n')
		if Δ.ψ ∈ (γ.ϕ for γ in Γ)
			println("Target reached!")
			break
		end
		while true
			nd_rule, nd_args = prompt_nd()
			γ = nd_rule(Γ, nd_args...)
			if γ ≠ nothing
				push!(Γ, γ)
				break
			end
			println("Ill-formed natural deduction rule, try again.")
		end
	end
end

main(ARGS)

# println(parse_sequent(length(ARGS) ≥ 1 ? ARGS[1] : "a & b"))
