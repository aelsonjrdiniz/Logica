```als
sig Pessoa{}

// Todo professor possuirá um conjunto de disciplinas associadas a ele
sig Professor extends Pessoa{
	disciplinas: set Disciplina
}

abstract sig Laboratorio{}

one sig Lcc1, Lcc2 extends Laboratorio{}

// Cada disciplina possuirá 2 horários
sig Disciplina{
	horario1: one Horario,
	horario2: one Horario
}

// Cada horário será composto por um dia e uma hora
sig Horario{
	dia: one Dia,
	hora: one Hora
}

abstract sig Dia{}

one sig Segunda, Terca, Quarta, Quinta, Sexta extends Dia{}

abstract sig Hora{}

one sig h8_10, h10_12, h14_16, h16_18 extends Hora{}

abstract sig Solicitacao {
	pessoa:Pessoa,
	laboratorio:Laboratorio,
	h1:Horario,
	h2:Horario,
	disciplina: set Disciplina
}

sig Reserva extends Solicitacao{}

sig ListaDeEspera extends Solicitacao{}

pred ehProfessor[p:Pessoa] {
	p in Professor
}

pred solicitacoesPossuemUmHorarioIgual[s1:Solicitacao, s2:Solicitacao] {
	(s1.h1 = s2.h1) or (s1.h1 = s2.h2) or (s1.h2 = s2.h2) or (s1.h2 = s2.h1) 
}

pred horariosSaoIguais[h1:Horario, h2:Horario] {
	(h1.hora = h2.hora) and (h1.dia = h2.dia)
}

pred disciplinaPossuiMesmoDia[h1:Horario, h2:Horario] {
	h1.dia = h2.dia
}

pred solicitacoesPossuemMesmoLaboratorio[s1:Solicitacao, s2:Solicitacao] {
	(s1.laboratorio = s2.laboratorio)
}

pred pessoaFezEsseSolicitacao[p: Pessoa, s: Solicitacao]{
	s.pessoa = p
}
pred solicitacaoNesseHorario[h: Horario, s: Solicitacao]{
	s.h1 = h or s.h2 = h
}
pred diasSaoIguais[d1: Dia, d2: Dia]{
	d1 = d2
}

fun getPrimeiroHorarioDisciplina[s:Solicitacao]: Horario {
	s.disciplina.horario1
}

fun getSegundoHorarioDisciplina[s:Solicitacao]: Horario {
	s.disciplina.horario2
}

fun getDisciplinasDoProfessor[p:Professor]: set Disciplina {
	p.disciplinas
}

fact { 
	some Pessoa
	some Professor
	some Solicitacao
	#Horario > 2
	#Reserva > 0
	#ListaDeEspera > 0
}

fact {
	// Não é possível que hajam menos disciplinas do que professores
	#Disciplina >= #Professor

	//Não podem haver 2 objetos da classe horário exatamente iguais
	all h1:Horario, h2:Horario | (h1 != h2) implies (not horariosSaoIguais[h1, h2])

	// Uma disciplina não pode ter 2 aulas no mesmo dia
	all d:Disciplina |  (not disciplinaPossuiMesmoDia[d.horario1, d.horario2])

	// Não é possível que uma disciplina possua 2 horários iguais
	all d:Disciplina | not horariosSaoIguais[d.horario1, d.horario2]

	// Qualquer solicitação possuirá 2 horários distintos se, e somente se, ela tiver sido feita por
	// um professor
	all s:Solicitacao | (ehProfessor[s.pessoa]) <=> (not horariosSaoIguais[s.h1, s.h2])

	// Caso a solicitação seja feita por um professor, ela possuirá 1 disciplina associada e
	// essa disciplina será obrigatoriamente uma das que o professor leciona
	all s:Solicitacao | (ehProfessor[s.pessoa]) implies ((#s.disciplina = 1) and 
		(s.disciplina in getDisciplinasDoProfessor[s.pessoa]))

	//Caso a solicitação não seja feita por um professor, não haverá nenhuma disciplina associada
	all s:Solicitacao | (not ehProfessor[s.pessoa]) implies (#s.disciplina = 0)

	// Caso a solicitação seja feita por um professor, os horários das reservas devem 
	// ser iguais aos horários da disciplina associada à reserva

	all s:Solicitacao | (ehProfessor[s.pessoa]) 
		implies (horariosSaoIguais[getPrimeiroHorarioDisciplina[s], s.h1])
	all s:Solicitacao | (ehProfessor[s.pessoa]) 
		implies (horariosSaoIguais[getSegundoHorarioDisciplina[s], s.h2])

	//Professores têm preferência na reserva
	all l:ListaDeEspera, r:Reserva | ((ehProfessor[l.pessoa]) and (solicitacoesPossuemUmHorarioIgual[l, r]))
		implies (ehProfessor[r.pessoa])
	
	//Não podem haver 2 reservas no mesmo horário no mesmo laboratório
	all r1:Reserva, r2:Reserva | (r1 != r2) implies (not (solicitacoesPossuemUmHorarioIgual[r1, r2] and
		(solicitacoesPossuemMesmoLaboratorio[r1, r2])))

	//Toda disciplina tem que ter um professor associado
	all d:Disciplina | #disciplinas.d > 0

	//Não existirá uma lista de espera em um horário livre
	all l:ListaDeEspera | one r1:Reserva, r2:Reserva | (solicitacoesPossuemUmHorarioIgual[l,r1])
		and (solicitacoesPossuemUmHorarioIgual[l, r2]) and r1.laboratorio = Lcc1
			and r2.laboratorio = Lcc2

	//Uma pessoa não pode ter 2 solicitações no mesmo horário
	all s1:Solicitacao, s2:Solicitacao | (s1.pessoa = s2.pessoa and s1 != s2) implies
		(not solicitacoesPossuemUmHorarioIgual[s1, s2])

	// toda pessoa deve haver uma solicitação
	all p: Pessoa | some s: Solicitacao | pessoaFezEsseSolicitacao[p,s]


}

assert propriedades{
	all s:Solicitacao | (ehProfessor[s.pessoa]) implies (some s.disciplina)
	all s:Solicitacao | (not ehProfessor[s.pessoa]) implies (no s.disciplina)
	
	#Reserva = 1 implies #ListaDeEspera = 0
	
} 

run{} for 5
```
