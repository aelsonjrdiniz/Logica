# Logica

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

sig Reserva{
	pessoa:Pessoa,
	laboratorio:Laboratorio,
	h1:Horario,
	h2:Horario,
	disciplina: set Disciplina
}

sig ListaDeEspera extends Reserva{}

pred ehProfessor[p:Pessoa] {
	p in Professor
}

pred PossuemUmHorarioIgual[r1:Reserva, r2:Reserva] {
	(horariosSaoIguais[r1.h1, r2.h1]) or (horariosSaoIguais[r1.h2, r2.h2])
}

pred horariosSaoIguais[h1:Horario, h2:Horario] {
	(h1.hora = h2.hora) and (h1.dia = h2.dia)
}

pred disciplinaPossuiMesmoDia[h1:Horario, h2:Horario] {
	h1.dia = h2.dia
}

fun getHorario1Disciplina[r:Reserva]: Horario {
	r.disciplina.horario1
}

fun getHorario2Disciplina[r:Reserva]: Horario {
	r.disciplina.horario2
}

fact { 
	some Pessoa
	some Professor
	some Disciplina
	some Reserva
	some ListaDeEspera
}

fact {
	// Não é possível que hajam menos disciplinas do que professores
	#Disciplina >= #Professor
	all p:Professor | #p.disciplinas > 0

	// Uma disciplina não pode ter 2 aulas no mesmo dia
	all d:Disciplina |  (not disciplinaPossuiMesmoDia[d.horario1, d.horario2])

	// Não é possível que uma disciplina possua 2 horários iguais
	all d:Disciplina | not horariosSaoIguais[d.horario1, d.horario2]

	// A reserva possuirá 2 horários distintos se, e somente se, ela tiver sido feita por
	// um professor
	all r:Reserva | (ehProfessor[r.pessoa]) <=> (not horariosSaoIguais[r.h1, r.h2])
	
	// Caso a reserva seja feita por um professor, ela possuirá 1 disciplina associada
	all r:Reserva | (ehProfessor[r.pessoa]) implies (#r.disciplina = 1)

	//Caso a reserva não seja feita por um professor, não haverá nenhuma disciplina associada
	all r:Reserva | (not ehProfessor[r.pessoa]) implies (#r.disciplina = 0)

	// Caso a reserva seja feita por um professor, os horários das reservas devem 
	// ser iguais aos horários da disciplina associada à reserva

	all r:Reserva | (ehProfessor[r.pessoa]) 
		implies (horariosSaoIguais[getHorario1Disciplina[r], r.h1])
	all r:Reserva | (ehProfessor[r.pessoa]) 
		implies (horariosSaoIguais[getHorario2Disciplina[r], r.h2])

	//Professores têm preferência na reserva
	all l:ListaDeEspera, r:Reserva | ((ehProfessor[l.pessoa]) and (PossuemUmHorarioIgual[l, r]))
		implies (ehProfessor[r.pessoa])
	
}

assert propriedades{
	all r:Reserva | (ehProfessor[r.pessoa]) implies (some r.disciplina)
	all r:Reserva | (not ehProfessor[r.pessoa]) implies (no r.disciplina)

}

run{}
