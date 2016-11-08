# ReNFA
Implementazione di un compilatore di espressioni regolari in automa non deterministico in linguaggio logico PROLOG

UNIMIB
Linguaggi di Programmazione A.A. 2014/2015

********************************************************************************************************************
**************************************************PREFAZIONE********************************************************


Abbiamo tentato di implementare la negazione di automi prevista da bar(RE) e abbiamo ottenuto i seguenti risultati:
Il programma riconosce comunque qualunque tipo di espressione regolare, e provvede comunque alla compilazione dell'
automa in qualunque caso.

Purtroppo il riconoscimento dell'input ha alcuni problemi per automi associati ad alcuni
tipi di espressioni regolari.
Più in generale, la nostra implementazione riesce a compilare automi (funzionanti anche nel momento del
riconoscimento dell'input) 

				SOLO 

nel caso in cui l'espressione associata all'automa è:

.bar(ATOM) dove ATOM è un atomo di Prolog;
.bar(RE) dove RE è una tra le espressioni regolari che seguono:

- seq(ATOM1,ATOM2,..ATOMn)
- star(ATOM)
- plus(ATOM)
- alt(ATOM1, ATOM2)
- oneof(ATOM1, ATOM2)
- bar(ATOM)

dove ATOM è un atomo di Prolog.


Purtroppo, invece non siamo riusciti ad ottenere dei risultati corretti, nel riconoscimento dell'input, per
espressioni regolari più complesse, quali:

.seq(bar(RE),RE2)
.star(bar(RE))
.plus(bar(RE))
.alt(bar(RE))

dove RE sono espressioni regolari atomiche, sia non atomiche.

.bar(seq(RE1,RE2,..REn))
.bar(star(RE))
.bar(plus(RE))
.bar(alt(RE1, RE2))
.bar(bar(RE))

dove RE sono espressioni regolari non atomiche.



Il programma è comunque in grado di funzionare correttamente, sia nella compilazione di automi che nel
riconoscimento dell'input
	
						IN QUALUNQUE CASO

che non coinvolga la negazione bar(RE) all'interno dell'espressione regolare.

******************************************************************************************************************
******************************************************************************************************************


-----------------------------------------------INTRODUZIONE--------------------------------------------------------

Lo scopo del progetto era implementare in prolog un compilatore da regexps (espressione regolare) a NFA.
I predicati richiesti erano:

.is_regexp/1
.nfa_regexp_compile/2
.nfa_recognize/2
.nfa_clear/0
.nfa_clear_nfa/1
.nfa_list/0
.nfa_list/1

Denoteremo con *, all'interno di questo file, i predicati qui sopra elencati.
Questo file richiama i 4 momenti tipici dell'esecuzione del codice, associando loro i predicati (richiesti e
ausiliari) utilizzati per l'implementazione; elenchiamo ora i 4 momenti e il relativo predicato "richiesto"
corrispondente:

1 - RICONOSCIMENTO DI ESPRESSIONI REGOLARI -> is_regexp/1
2 - COSTRUZIONE DI AUTOMI -> nfa_compile_regexp_/2
2bis - COSTRUZIONE DI AUTOMI NEGATI
3 - RICONOSCIMENTO DI INPUT -> nfa_recognize/2
4 - GESTIONE DI AUTOMI PRECEDENTEMENTE DEFINITI -> nfa_clear/0, nfa_clear_nfa/1, nfa_list/0, nfa_list/1


..............................1^ PARTE -> RICONOSCIMENTO DI ESPRESSIONI REGOLARI.................................

       *.is_regexp/1 (costruito in modo diverso per RE atomiche e non atomiche) 
		Riconoscimento di espressioni regolari costituite da numeri e atomi di Prolog.
		Gestione degli errori nel caso di un'espressione regolare non riconosciuta.	
	
	.is_regexp_NA/1 (Costruito in maniera differente per ogni RE non atomica)
		Riconoscimento delle espressioni regolari non atomiche.

	STAR (RE= star(RE)) -> riconoscimento chiusura di kleene con 0 o piu ripetizioni
	PLUS (RE= plus(RE)) -> riconoscimento chiusura di kleene con almeno una ripetizione
	SEQ (RE= seq(RE1, RE2,...,REs)) -> riconoscimento per la sequenza di regexp
	BAR (RE) -> negazione di automi
	ALT (RE= alt(RE1, RE2,...,REs)) -> riconoscimento per l'unione delle regexp
	ONEOF (RE=oneof(ATOM1, ATOM2,...,ATOMs)) -> indica la scelta tra i simboli ATOM.

	In quest'ultimo, è necessario l'utilizzo di un ulteriore predicato per verificare che
	tutti gli elementi di ALT siano atomici.

	.is_regexp_NA_ONEOF/1
		Riconoscimento di espressioni regolari del tipo oneof.
 
.....................................2^ PARTE -> COSTRUZIONE DI AUTOMI.........................................,..

Prima del codice relativo alla compilazione di un automa NFA, elenchiamo i 7 predicati per la costruzione
dinamica degli automi.

	:- dynamic nfa_initial/2.
		
		Inizializza uno stato dell'automa FA_Id come iniziale: nfa_initial(automa, stato)
	
	:- dynamic nfa_final/2.	

		Inizializza uno stato dell'automa FA_Id come finale: nfa_final(automa,stato)

	:- dynamic nfa_error/2
		
		Inizializza uno stato dell'automa FA_Id come stato di errore: nfa_error(automa,stato)

	:- dynamic nfa_delta/4.

		Inizializza la funzione delta che associa, in un automa, ad uno stato qn uno stato qm.
		Posso passare da qn a qm tramite un atomo: nfa_delta(automa,staton,atomo,statom)
	
	:- dynamic nfa_delta_epsilon/3
	
		Inizializza la funzione delta che associa, in un automa, ad uno stato qn uno stato qm.
		Posso passare da qn a qm tramite epsilon mosse: nfa_delta_epsilon(automa,staton,statom)

	:- dynamic nfa_delta_bar/3
		
		Inizializza la funzione delta, specifica per la negazione di espressione regolare,
		che associa, in un automa, ad uno stato qn uno stato qm. Posso passare da qn a qm tramite un
		input che non è	implicato nella negazione; nfa_delta_bar(automa,staton,statom)

	:- dynamic nfa_illegal_delta_bar/4
		Inizializza la funzione delta, specifica per la negazione diespressione regolare, che associa,
		in un automa, ad uno stato qn uno stato qm. Associo qn a qm tramite l'espressione regolare che
		devo negare: nfa_illegal_delta_bar(automa,staton,atomo,statom)



Elenchiamo ora i predicati non dinamici necessari alla compilazione dell'automa NFA.

	.check_ID/1
			
		Predicato secondario per il controllo di un'eventuale definizione precedente di un automa
		con lo stesso FA_Id, per evitare incongruenze e ambiguità nella compilazione.


      * .nfa_compile_regexp/2

		 Controllo di un'eventuale definizione precedentedi un automa con lo stesso nome(check_ID/1).
		 Verifica della regolarità di RE (is_regexp) e definizione degli stati iniziale e finale
		 (nfa_initial e nfa_final). Prepararazione (reset_gensym) per la creazione degli stati intermedi.
		 Definizione dell'automa che riconoscerà la mia grammatica (build_nfa/4):
		 successivamente la definizione sarà diversaper ogni espressione regolare che posso compilare.

	.build_nfa/4 (costruito in modo diverso per RE atomiche e non atomiche)

		Effettiva definizione dell'automa richiesto, tramite asserzioni di predicati dinamici.
		Utilizzo il PREDICATO gensym/2 per la generazione dinamica degli stati intermedi.
		Utilizzo il PREDICATO assert/1 per la definizione della funzione delta.
		
	.build_nfa_NA/4 (costruito in modo diverso per ogni tipo di RE non atomica)
		
		Compilazione di automi per espressioni regolari non atomiche.
		Utilizzo il PREDICATO gensym/2 per la generazione dinamica degli stati intermedi.
		Utilizzo il PREDICATO assert/1 per la definizione della funzione delta.
			

...................................2bis^ PARTE -> COSTRUZIONE DI AUTOMI NEGATI.................................,..

	.build_nfa_BAR/4 (costruito in modo diverso per RE atomiche e non atomiche)

		Effettiva definizione dell'automa richiesto, tramite asserzioni di predicati dinamici.
		Utilizzo il PREDICATO gensym/2 per la generazione dinamica degli stati intermedi.
		Utilizzo il PREDICATO assert/1 per la definizione della funzione delta.
		
	.build_nfa_NA_BAR/4 (costruito in modo diverso per ogni tipo di RE non atomica)
		
		Compilazione di automi per espressioni regolari non atomiche.
		Utilizzo il PREDICATO gensym/2 per la generazione dinamica degli stati intermedi.
		Utilizzo il PREDICATO assert/1 per la definizione della funzione delta.


.....................................3^ PARTE -> RICONOSCIMENTO DI INPUT..........................................

Elenchiamo ora i predicati necessari al riconoscimento dell'input tramite l'automa NFA.


       *.nfa_recognize/2

	Verifica che l'input sia effettivamente una parola accettata dall' automa e
	gestione di eventuali incompatibilità.

	.nfa_check/3

	Verifico che nell'automa FA_Id, tramite la funzione delta, considerando carattere per carattere il mio
	input (nfa_delta_epsilon) posso arrivare ad uno stato che sia finale (nfa_final). Se così fosse, il mio
	input sarà accettato da FA_Id.


....................................4^ PARTE -> GESTIONE DEGLI NFA GIA' DEFINITI..................................

Elenchiamo ora i predicati necessari alla gestione degli automi già definiti, alla loro cancellazione e alla loro
visitazione.

	* .nfa_clear/0 e nfa_clear_nfa/1

		Eliminazione degli automi/dell'automa già definiti/o in memoria e gestione degli errori
		in caso di automi/a inesistenti/e.


	* .nfa_list/0 e nfa_list/1

		Elencazione degli stati iniziali, finali e delle funzioni delta di tutti gli automi
		precedentemente definiti e gestione degli errori in caso di automa inesistente.
	
  	  .check_ID_listing/1

		Controllo di una eventuale definizione precedente di un automa con lo stesso FA_Id,
		per poterlo listare o, eventualmente, restituire un errore.
