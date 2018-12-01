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

function Base.show(io::IO, ϕ::Literal)
	print(io, typeof(ϕ) == True ? 'T' : '┴')
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

strip_parens(ϕ, parens) = !isempty(ϕ) && ϕ[[1, end]] == parens ? begin
	ϕ⁺ = ϕ[2:end-1]
	balanced_parens(ϕ⁺) ? ϕ⁺ : ϕ
end : ϕ
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

mutable struct ProofStep
	indent::Bool
	ϕ::Formula
	rationale::String
	outdent::Int
end

ProofStep(ϕ::Formula, rationale::AbstractString) = ProofStep(false, ϕ, rationale, 0)
ProofStep(indent::Bool, ϕ::Formula, rationale::AbstractString) = ProofStep(indent, ϕ, rationale, 0)
ProofStep(ϕ::Formula, rationale::AbstractString, outdent::Int) = ProofStep(false, ϕ, rationale, outdent)

(Γ::Array{ProofStep})(i::Int64) = Γ[i].ϕ

function dent_balance(Γ::Array{ProofStep}, ante, subseq=length(Γ) + 1; d=0)
	if ante < subseq ≤ length(Γ) + 1
		d -= Γ[ante].outdent
		if d ≥ 0
			for i ∈ ante+1:subseq-1
				d += Γ[i].indent - Γ[i].outdent
				if d < 0
					return
				end
			end
			return d
		end
	end
end

Γ::Array{ProofStep} ≡ ante::Int =
	dent_balance(Γ, ante) ≠ nothing

is_subproof(Γ::Array{ProofStep}, ante, subseq) =
	Γ[ante].indent && Γ[subseq].outdent ≠ 0 &&
	(ante == subseq || dent_balance(Γ, ante, subseq) == 0)

Γ::Array{ProofStep} ≡ I::Array{Int} =
	is_subproof(Γ, I...) &&
	dent_balance(Γ, I[2]; d=1) ≠ nothing

function andi(Γ, i, j)
	if Γ ≡ i && Γ ≡ j
		ProofStep(Γ(i) ∧ Γ(j), "^ᵢ, $i, $j")
	end
end

function ande1(Γ, i)
	if Γ ≡ i
		ϕ = Γ(i)
		if typeof(ϕ) == And
			ProofStep(ϕ.ϕ₁, "^ₑ₁, $i")
		end
	end
end

function ande2(Γ, i)
	if Γ ≡ i
		ϕ = Γ(i)
		if typeof(ϕ) == And
			ProofStep(ϕ.ϕ₂, "^ₑ₂, $i")
		end
	end
end

function ori1(Γ, i, ψ=nothing)
	if ψ ≠ nothing && Γ ≡ i
		ψ = parse_formula(ψ)
		ProofStep(Γ(i) ∨ ψ, "vᵢ₁, $i")
	end
end

function ori2(Γ, i, ψ=nothing)
	if ψ ≠ nothing && Γ ≡ i
		ψ = parse_formula(ψ)
		ProofStep(ψ ∨ Γ(i), "vᵢ₂, $i")
	end
end

function ore(Γ, i, J, K)
	j₁, j₂ = J
	k₁, k₂ = K
	if Γ ≡ i && Γ ≡ J && Γ ≡ K
		χ₁ = Γ(j₂)
		χ₂ = Γ(k₂)
		if typeof(Γ(i)) == Or && χ₁ == χ₂
			ProofStep(χ₁, "vₑ, $i, $j₁-$j₂, $k₁-$k₂")
		end
	end
end

function impi(Γ, I)
	i₁, i₂ = I
	if Γ ≡ I
		ProofStep(Γ(i₁) → Γ(i₂), "→ᵢ, $i₁-$i₂")
	end
end

function impe(Γ, i, j)
	if Γ ≡ i && Γ ≡ j
		ϕ = Γ(i)
		if typeof(ϕ) == Imp && Γ(j) == ϕ.ϕ₁
			ProofStep(ϕ.ϕ₂, "→ₑ, $i, $j")
		end
	end
end

function negi(Γ, I)
	i₁, i₂ = I
	if Γ ≡ I && Γ(i₂) == False()
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

function bote(Γ, i, ψ=nothing)
	if ψ ≠ nothing && Γ ≡ i && Γ(i) == False()
		ψ = parse_formula(ψ)
		ProofStep(ψ, "┴ₑ, $i")
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
	if Γ ≡ I && Γ(i₂) == False()
		ϕ = Γ(i₁)
		if typeof(ϕ) == Neg
			ProofStep(ϕ.ϕ, "PBC, $i₁, $i₂")
		end
	end
end

function LEM(Γ, ψ=nothing)
	if ψ ≠ nothing
		ψ = parse_formula(ψ)
		ProofStep(ψ ∨ ¬ψ, "LEM")
	end
end

function assume(Γ, ψ=nothing)
	if ψ ≠ nothing
		ψ = parse_formula(ψ)
		ProofStep(true, ψ, "Assumption")
	end
end

function conclude(Γ)
	if dent_balance(Γ, 1; d=Γ[1].indent) ≥ 1
		Γ[end].outdent += 1
	end
end

function undo(Γ)
	if length(Γ) ≥ 1
		if Γ[end].outdent ≥ 1
			Γ[end].outdent -= 1
			return false
		else
			return true
		end
	end
end

function copy(Γ, i)
	if Γ ≡ i
		ProofStep(Γ(i), "Copy $i")
	end
end

nd_rules = String.(Symbol.((andi, ande1, ande2,
							ori1, ori2, ore,
							impi, impe,
							negi, nege,
							bote,
							negnegi, negnege,
							MT, PBC, LEM,
							assume, conclude, undo,
							copy)))

isnumstr(str) = all(isdigit(x) for x ∈ str)
hasnum(str) = any(isdigit(x) for x ∈ str)

function prompt_nd()
	inp = input("Natural deduction: ")
	rule_args = map(strip, split(inp, r",|\s+", keepempty=false, limit=2))
	rule = rule_args[1]
	args = length(rule_args) ≥ 2 ? rule_args[2] : ""
	
	if rule ∉ nd_rules
		println("Unknown rule >", rule, "<, please retry")
		return prompt_nd()
	end

	function arg_switch(m)
		if isnumstr(m)
			parse(Int, m)
		elseif hasnum(m)
			parse.(Int, split(m, '-'))
		else
			parse_formula(m)
		end
	end

	argregex = r"(?:\d+-\d+)|\d+|[^\d,]+"
	args = arg_switch.(filter(!isempty, strip.(getfield.(eachmatch(argregex, args), :match))))
	
	return eval(Symbol(rule)), args
end

function Base.show(io::IO, γ::ProofStep)
	print(io, γ.ϕ, "\t(", γ.rationale, ")")
end

function Base.show(io::IO, Γ::Array{ProofStep})
	if isempty(Γ)
		println("[intentionally left blank]")
		return
	end

	widind = length(digits(length(Γ)))

	ϕstrs = [repr(γ.ϕ) for γ ∈ Γ]
	ratstrs = getfield.(Γ, :rationale)

	widϕ = maximum(length.(ϕstrs))
	widrat = maximum(length.(ratstrs))

	indent = 0
	for (i, γ) ∈ enumerate(Γ)
		if γ.indent
			println(' ' ^ (widind + 2),
					"|  " ^ indent,
					'┌', '─' ^ (widϕ + 6 + widrat), '┐')
			indent += 1
		end
		println(' ' ^ (widind - length(digits(i))), i, ". ",
				"|  " ^ indent,
				ϕstrs[i],
				' ' ^ (widϕ + widrat - length(ϕstrs[i]) - length(ratstrs[i]) + 2),
				ratstrs[i],
				indent ≥ 1 ? "  |" : "")
		for i ∈ 1:γ.outdent
			indent -= 1
			println(' ' ^ (widind + 2),
					"|  " ^ indent,
					'└', '─' ^ (widϕ + 6 + widrat), '┘')
		end
	end
end

function print_title()
	println("=== Interactive Propositional Logic Engine using Natural Deduction ===\n")
end

function clear(entirely=false)
	# println("\33[2J")
	run(`cmd /c cls`)
	if !entirely
		print_title()
	end
end

function accomplished(Γ, ψ)
	d = 0
	for γ ∈ Γ
		d += γ.indent
		if d == 0 && γ.ϕ == ψ
			return true
		end
		d -= γ.outdent
	end
	return false
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
		if accomplished(Γ, Δ.ψ)
			println("Target reached!")
			break
		end
		while true
			nd_rule, nd_args = prompt_nd()
			γ = nd_rule(Γ, nd_args...)
			if γ ≠ nothing
				if nd_rule == undo
					if γ == true
						Γ = Γ[1:end-1]
					end
				elseif typeof(γ) ≠ Int
					push!(Γ, γ)
				end
				break
			end
			println("Ill-formed natural deduction rule, try again.")
		end
	end
end

main(ARGS)

# println(parse_sequent(length(ARGS) ≥ 1 ? ARGS[1] : "a & b"))
