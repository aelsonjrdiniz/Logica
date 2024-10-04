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

//Cada solicitação possuirá a pessoa que a fez, o laboratório solicitado 
//e o(s) horário(s) e a disciplina associada, caso ela exista
abstract sig Solicitacao {
	pessoa: Pessoa,
	laboratorio:Laboratorio,
	horarios: set Horario,
	disciplina: set Disciplina
}

sig Reserva extends Solicitacao{}

sig ListaDeEspera extends Solicitacao{}

pred ehProfessor[p:Pessoa] {
	p in Professor
}

pred possuemUmHorarioIgual[s1:Solicitacao, s2:Solicitacao] {
	some h:Horario | h in s1.horarios and h in s2.horarios
}

pred horariosSaoIguais[h1:Horario, h2:Horario] {
	(h1.hora = h2.hora) and (h1.dia = h2.dia)
}

pred possuiAulaMesmoDia[d:Disciplina] {
	d.horario1.dia = d.horario2.dia
}

pred possuemMesmoLaboratorio[s1:Solicitacao, s2:Solicitacao] {
	(s1.laboratorio = s2.laboratorio)
}

pred horarioEstaOcupado[l:ListaDeEspera, r1:Reserva, r2:Reserva] {
	(possuemUmHorarioIgual[l,r1]) and (possuemUmHorarioIgual[l, r2]) 
		and r1.laboratorio = Lcc1	and r2.laboratorio = Lcc2
}

pred horariosConflitam[d1:Disciplina, d2:Disciplina] {
	d1.horario1 = d2.horario1 or d1.horario2 = d2.horario2 or d1.horario1 = d2.horario2
		or d1.horario2 = d2.horario1
}

fun disciplinasDoProfessor[p:Professor]: set Disciplina {
	p.disciplinas
}

fact {

	//Não podem haver 2 horários exatamente iguais
	all h1:Horario, h2:Horario | (h1 != h2) implies (not horariosSaoIguais[h1, h2])

	// Uma disciplina não pode ter 2 aulas no mesmo dia
	all d:Disciplina |  (not possuiAulaMesmoDia[d])

	//Não existe disciplina sem professor
	all d:Disciplina | #disciplinas.d > 0
	
	//Um professor não pode dar 2 ou mais disciplinas no mesmo horário
	all p:Professor, d1:Disciplina, d2:Disciplina | 
		(d1 in disciplinasDoProfessor[p] and d2 in disciplinasDoProfessor[p] and d1 != d2) =>			
			not horariosConflitam[d1, d2]		

}

fact {

	// Qualquer solicitação possuirá 2 horários se, e somente se, ela tiver sido feita por
	// um professor
	all s:Solicitacao | (ehProfessor[s.pessoa]) <=> (#s.horarios = 2)
	
	//Qualquer solicitação possuirá 1 horário apenas se, e somente se, ela tiver sido feita por
	//alguém que não é professor
	all s:Solicitacao | (not ehProfessor[s.pessoa]) <=> (#s.horarios = 1)

	// Caso a solicitação seja feita por um professor, ela possuirá 1 disciplina associada e
	// essa disciplina será obrigatoriamente uma das que o professor leciona
	all s:Solicitacao | (ehProfessor[s.pessoa]) implies ((#s.disciplina = 1) and 
		(s.disciplina in disciplinasDoProfessor[s.pessoa]))

	//Caso a solicitação não seja feita por um professor, não haverá nenhuma disciplina associada
	all s:Solicitacao | (not ehProfessor[s.pessoa]) implies (#s.disciplina = 0)

	//Professores têm preferência na reserva
	all l:ListaDeEspera, r:Reserva | ((ehProfessor[l.pessoa]) and (possuemUmHorarioIgual[l, r]))
		implies (ehProfessor[r.pessoa])
	
	//Não podem haver 2 reservas no mesmo horário no mesmo laboratório
	all r1:Reserva, r2:Reserva | (r1 != r2) implies (not (possuemUmHorarioIgual[r1, r2] and
		(possuemMesmoLaboratorio[r1, r2])))

	//Não existirá uma lista de espera em um horário livre
	all l:ListaDeEspera | one r1:Reserva, r2:Reserva | (r1 != r2) and horarioEstaOcupado[l, r1, r2]

	//Uma pessoa não pode ter 2 solicitações no mesmo horário
	all s1:Solicitacao, s2:Solicitacao | (s1.pessoa = s2.pessoa and s1 != s2) implies
		(not possuemUmHorarioIgual[s1, s2])

}

assert propriedades{
	
	//Não existe um professor sem disciplina que reserva um laboratório
	no p:Professor | some s:Solicitacao | #p.disciplinas = 0 and p in s.pessoa

	//Não existe uma solicitação com 2 horários no mesmo dia
	all s:Solicitacao | some h1:s.horarios, h2:s.horarios | (#s.horarios = 2 and h1 != h2) implies 
		(h1.dia != h2.dia)

	//Não existe uma lista de espera para um dos laboratórios em um horário caso
	//o outro laboratório esteja livre no mesmo horário
	all l:ListaDeEspera | one r1:Reserva, r2:Reserva | (possuemUmHorarioIgual[l,r1])
		and (possuemUmHorarioIgual[l, r2]) and r1.laboratorio = Lcc1
			and r2.laboratorio = Lcc2

	// Apenas professores podema associar disciplinas na reserva
	all s:Solicitacao | (s.pessoa not in Professor) implies #s.disciplina = 0
	
	// Apenas professores podem ter 2 horários na mesma reserva
	all s:Solicitacao | (s.pessoa not in Professor) implies #s.horarios = 1

	// Não existe um cenário onde um professor esteja na lista de espera por um horário
	// enquanto alguém que não é professor está com aquele horário reservado
	no l:ListaDeEspera, r:Reserva| (ehProfessor[l.pessoa] and possuemUmHorarioIgual[l, r]) and not ehProfessor[r.pessoa] 

} 

check propriedades
//run{} for 5

```
