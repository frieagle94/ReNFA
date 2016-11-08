% PREDICATO is_regexp/1
% riconoscimento di espressioni regolari costituite da numeri e atomi di
% Prolog
is_regexp(RE) :- atomic(RE),!.
 
% PREDICATO is_regexp_NA/1
% Riconoscimento delle espressioni regolari non atomiche
is_regexp(RE) :- RE =.. REop, is_regexp_NA(REop),!.
 
% Gestione errori del riconoscimento.
is_regexp(RE):- !,write('ERROR: Impossible to recognize the Regular Expression '),
    write(RE),write('!'),fail.
 
%is_regexp_NA per RE= star(RE)
is_regexp_NA([star|[RE]]) :- is_regexp(RE).
 
%is_regexp_NA per RE= plus(RE)
is_regexp_NA([plus|[RE]]) :- is_regexp(RE).
 
%is_regexp_NA per RE= bar(RE)
is_regexp_NA([bar|[RE]]) :- is_regexp(RE).
 
%is_regexp_NA per RE= seq(RE1, RE2,...,REs)
is_regexp_NA([seq|[]]).
is_regexp_NA([seq|RE]) :- RE=[RE1|RE2],
    is_regexp(RE1), is_regexp_NA([seq|RE2]).
 
%is_regexp_NA per RE= alt(RE1, RE2,...,REs)
is_regexp_NA([alt|[]]).
is_regexp_NA([alt|RE]) :- RE=[RE1|RE2],
    is_regexp(RE1), is_regexp_NA([alt|RE2]).
 
%is_regexp_NA per RE=oneof(ATOM1, ATOM2,...,ATOMs)
% Nel riconoscimento dell'RE oneof devo utilizzare
% un'ulteriore predicato per verificare che tutti gli argomenti di
% alt siano atomici.
is_regexp_NA([oneof|[]]).
is_regexp_NA([oneof|RE]) :- RE=[RE1|RE2],
    atomic(RE1), is_regexp_NA_ONEOF(RE2).
 
% PREDICATO is_regexp_NA_ONEOF/1
is_regexp_NA_ONEOF([]).
is_regexp_NA_ONEOF(RE) :- RE=[RE1|RE2],
    atomic(RE1), is_regexp_NA_ONEOF(RE2).
 
% Definizione dei 7 predicati necessari per la costruzione dinamica
% degli automi
 
% PREDICATO DINAMICO nfa_initial/2
% Inizializza uno stato dell'automa FA_Id come iniziale.
% nfa_initial(automa, stato)
:- dynamic nfa_initial/2.
 
% PREDICATO DINAMICO nfa_final/2
% Inizializza uno stato dell'automa FA_Id come finale.
% nfa_final(automa,stato)
:- dynamic nfa_final/2.
 
% PREDICATO DINAMICO nfa_error/2
% Inizializza uno stato dell'automa FA_Id come stato di errore.
% nfa_error(automa,stato)
:- dynamic nfa_error/2.
 
% PREDICATO DINAMICO nfa_delta/4
% Inizializza la funzione delta che associa, in un automa, ad uno stato
% qn uno stato qm. Posso passare da qn a qm tramite un atomo.
% nfa_delta(automa,staton,atomo,statom)
:- dynamic nfa_delta/4.
 
% PREDICATO DINAMICO nfa_delta_epsilon/3
% Inizializza la funzione delta che associa, in un automa, ad uno stato
% qn uno stato qm. Posso passare da qn a qm tramite epsilon mosse.
% nfa_delta(automa,staton,statom)
:- dynamic nfa_delta_epsilon/3.
 
% PREDICATO DINAMICO nfa_delta_bar/3
% Inizializza la funzione delta, specifica per la negazione di
% espressione regolare, che associa, in un automa, ad uno stato qn uno
% stato qm. Posso passare da qn a qm tramite un input che non è
% implicato nella negazione.
% nfa_delta(automa,staton,statom)
:- dynamic nfa_delta_bar/3.
 
% PREDICATO DINAMICO nfa_illegal_delta_bar/4
% Inizializza la funzione delta, specifica per la negazione di
% espressione regolare, che associa, in un automa, ad uno stato qn uno
% stato qm. Associo qn a qm tramite l'espressione regolare che
% devo negare.
% nfa_delta(automa,staton,atomo,statom)
:- dynamic nfa_illegal_delta_bar/4.
 
 
% PREDICATO check_ID/1
% Controllo un'eventuale definizione precedente di un automa con lo
% stesso FA_Id, per evitare incongruenze e ambiguità.
check_ID(FA_Id):- not(nfa_initial(FA_Id,_)),!.
check_ID(FA_Id):- write('ERROR: The AUTOMA '),write(FA_Id),
    write(' is still defined in memory!'),fail.
 
% PREDICATO nfa_compile_regexp/2
% Con nfa_compile_regexp controllo un'eventuale definizione precedente
% di un automa con lo stesso nome(check_ID/1).
% Verifico la regolarità di RE (is_regexp)e
% poi imposto gli stati iniziale e finale (nfa_initial e nfa_final),
% oltre che preparare (reset_gensym) la creazione degli stati intermedi.
% Inoltre definisco l'automa che riconoscerà la mia
% grammatica (build_nfa/4): successivamente la definizione sarà diversa
% per ogni espressione regolare che posso compilare.
nfa_compile_regexp(FA_Id,RE):-
    check_ID(FA_Id),
    is_regexp(RE),
    assert(nfa_initial(FA_Id,q0)),
    assert(nfa_final(FA_Id,qFin)),
    reset_gensym,
    build_nfa(FA_Id,q0,RE,qFin),
    write('The automa has been correctly compiled!').
 
% PREDICATO build_nfa/4(costruito in modo diverso per RE atomiche e non
% atomiche).
 
% build_nfa nel caso di compilazione di una RE atomica
build_nfa(FA_Id,In,RE,Fin):- atomic(RE),
    assert(nfa_delta(FA_Id,In,RE,Fin)),!.
 
% build_nfa nel caso di compilazione una RE non atomica(NA)
build_nfa(FA_Id,In,RE,Fin):- RE=..REapp,
    build_nfa_NA(FA_Id,In,REapp,Fin).
 
% PREDICATO build_nfa_NA/4(costruito in modo diverso per
% ogni diversa RE non atomica).
% Compilo su FA_Id una RE non atomica.
% Utilizzo il PREDICATO gensym/2 per la generazione dinamica degli stati
% intermedi.
% Utilizzo il PREDICATO assert/1 per la definizione della funzione
% delta.
 
%Definizione di build_nfa_NA per RE=seq(RE1,RE2,...)
build_nfa_NA(FA_Id,S,[seq|RE],N):- build_nfa_NA(FA_Id,S,seq(RE),N),!.
build_nfa_NA(FA_Id,S,seq([RE|[]]),Fin):- build_nfa(FA_Id,S,RE,Fin).
build_nfa_NA(FA_Id,S,seq([RE|REs]),N):-gensym(q,X),
    build_nfa(FA_Id,S,RE,X),
    build_nfa_NA(FA_Id,X,seq(REs),N),!.
 
%Definizione di build_nfa_NA per RE=star(RE)
build_nfa_NA(FA_Id,S,[star|[star(RE)]],N):-
    build_nfa_NA(FA_Id,S,[star|[RE]],N),!.
build_nfa_NA(FA_Id,S,[star|RE],N):-
    gensym(q,X),gensym(q,Y),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    assert(nfa_delta_epsilon(FA_Id,S,N)),
    assert(nfa_delta_epsilon(FA_Id,Y,N)),
    assert(nfa_delta_epsilon(FA_Id,Y,X)),
    assert(nfa_final(FA_Id,S)),
    build_nfa_NA(FA_Id,X,star(RE),Y),!.
build_nfa_NA(FA_Id,S,star([RE|[]]),Fin):- build_nfa(FA_Id,S,RE,Fin).
 
%Definizione di build_nfa_NA per RE=plus(RE)
build_nfa_NA(FA_Id,S,[plus|RE],N):-
    gensym(q,X),gensym(q,Y),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    assert(nfa_delta_epsilon(FA_Id,Y,N)),
    assert(nfa_delta_epsilon(FA_Id,Y,X)),
    build_nfa_NA(FA_Id,X,plus(RE),Y),!.
build_nfa_NA(FA_Id,S,plus([RE|[]]),Fin):- build_nfa(FA_Id,S,RE,Fin).
 
%Definizione di build_nfa_NA per RE=alt(RE1,RE2,...)
build_nfa_NA(FA_Id,S,[alt|RE],N):-
    build_nfa_NA(FA_Id,S,alt(RE),N),!.
build_nfa_NA(FA_Id,S,alt([RE|[]]),N):-
    gensym(q,X),gensym(q,Y),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    assert(nfa_delta_epsilon(FA_Id,Y,N)),
    build_nfa(FA_Id,X,RE,Y).
build_nfa_NA(FA_Id,S,alt([RE|REs]),N):-
    gensym(q,X),gensym(q,Y),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    assert(nfa_delta_epsilon(FA_Id,Y,N)),
    build_nfa(FA_Id,X,RE,Y),
    build_nfa_NA(FA_Id,S,alt(REs),N),!.
 
%Definizione di build_nfa_NA per RE=oneof(A1,A2,...)
build_nfa_NA(FA_Id,S,[oneof|RE],N):-
    build_nfa_NA(FA_Id,S,oneof(RE),N),!.
build_nfa_NA(FA_Id,S,oneof([RE|[]]),N):-
    gensym(q,X),gensym(q,Y),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    assert(nfa_delta_epsilon(FA_Id,Y,N)),
    build_nfa(FA_Id,X,RE,Y).
build_nfa_NA(FA_Id,S,oneof([RE|REs]),N):-
    gensym(q,X),gensym(q,Y),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    assert(nfa_delta_epsilon(FA_Id,Y,N)),
    build_nfa(FA_Id,X,RE,Y),
    build_nfa_NA(FA_Id,S,oneof(REs),N),!.
 
%Definizione di build_nfa_NA per RE=bar(RE)
build_nfa_NA(FA_Id,S,[bar|RE],N):-
    build_nfa_NA(FA_Id,S,bar(RE),N),!.
build_nfa_NA(FA_Id,S,bar([RE]),N):-
    assert(nfa_final(FA_Id,qFinBar)),
    assert(nfa_final(FA_Id,q0)),
    retract(nfa_final(FA_Id,qFin)),
    build_nfa_BAR(FA_Id,S,RE,N),!.
 
% PREDICATO build_nfa_BAR/4
% Costruito in maniera diversa per RE atomiche e non atomiche.
% Permette di implementare la negazione di RE,prevista da bar(RE)
 
% Definizione di build_nfa_BAR nel caso di compilazione di negazione di
% RE atomiche
build_nfa_BAR(FA_Id,In,RE,Fin):- atomic(RE),
    assert(nfa_delta(FA_Id,In,RE,Fin)),
    assert(nfa_delta_bar(FA_Id,Fin,qFinBar)),
    assert(nfa_delta_bar(FA_Id,qFinBar,qFinBar)),
    assert(nfa_illegal_delta_bar(FA_Id,In,RE,qFinBar)),
    assert(nfa_delta_bar(FA_Id,In,qFinBar)),!.
 
% Definizione di build_NFA_BAR nel caso di compilazione di negazione di
% RE non atomiche
build_nfa_BAR(FA_Id,In,RE,Fin):- RE=..REapp,
    build_nfa_BAR_NA(FA_Id,In,REapp,Fin).
 
% PREDICATO build_nfa_BAR_NA/4(costruito in modo diverso per
% ogni diversa RE non atomica).
% Compilo su FA_Id la negazione di una RE non atomica.
% Utilizzo il PREDICATO gensym/2 per la generazione dinamica degli stati
% intermedi.
% Utilizzo il PREDICATO assert/1 per la definizione della funzione
% delta.
 
%Definizione di build_nfa_BAR_NA per RE=seq(RE1,RE2,...,REs)
build_nfa_BAR_NA(FA_Id,S,[seq|RE],N):-
    build_nfa_BAR_NA(FA_Id,S,seq(RE),N).
build_nfa_BAR_NA(FA_Id,S,seq([RE|[]]),Fin):-
    build_nfa_BAR(FA_Id,S,RE,Fin),!.
build_nfa_BAR_NA(FA_Id,S,seq([RE|REs]),N):-gensym(q,X),
    assert(nfa_final(FA_Id,X)),
    build_nfa_BAR(FA_Id,S,RE,X),
    build_nfa_BAR_NA(FA_Id,X,seq(REs),N).
 
%Definizione di build_nfa_BAR_NA per RE=star(RE)
build_nfa_BAR_NA(FA_Id,S,[star|RE],N):-
    gensym(q,X),gensym(q,Y),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    assert(nfa_delta_epsilon(FA_Id,S,N)),
    assert(nfa_delta_epsilon(FA_Id,Y,N)),
    assert(nfa_delta_epsilon(FA_Id,Y,X)),
    build_nfa_BAR_NA(FA_Id,X,star(RE),Y).
build_nfa_BAR_NA(FA_Id,S,star([RE|[]]),Fin):-
    retract(nfa_final(FA_Id,q0)),
    assert(nfa_illegal_delta_bar(FA_Id,Fin,RE,qFinBar)),
    build_nfa_BAR(FA_Id,S,RE,Fin).
 
%Definizione di build_nfa_BAR_NA per RE=plus(RE)
build_nfa_BAR_NA(FA_Id,S,[plus|RE],N):-
    gensym(q,X),gensym(q,Y),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    assert(nfa_delta_epsilon(FA_Id,Y,N)),
    assert(nfa_delta_epsilon(FA_Id,Y,X)),
    build_nfa_BAR_NA(FA_Id,X,plus(RE),Y).
build_nfa_BAR_NA(FA_Id,S,plus([RE|[]]),Fin):-
    assert(nfa_illegal_delta_bar(FA_Id,Fin,RE,qFinBar)),
    build_nfa_BAR(FA_Id,S,RE,Fin),!.
 
%Definizione di build_nfa_BAR_NA per RE=alt(RE1,RE2,...,REs)
build_nfa_BAR_NA(FA_Id,S,[alt|RE],N):-
    gensym(q,X),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    build_nfa_BAR_NA(FA_Id,X,alt(RE),N).
build_nfa_BAR_NA(FA_Id,S,alt([RE|[]]),N):-
    gensym(q,X),
    assert(nfa_delta_epsilon(FA_Id,X,N)),
    assert(nfa_error(FA_Id,qFin)),
    build_nfa_BAR(FA_Id,S,RE,X),!.
build_nfa_BAR_NA(FA_Id,S,alt([RE|REs]),N):-
    gensym(q,X),
    assert(nfa_delta_epsilon(FA_Id,X,N)),
    build_nfa_BAR(FA_Id,S,RE,X),
    build_nfa_BAR_NA(FA_Id,S,alt(REs),N).
 
%Definizione di build_nfa_BAR_NA per RE=bar(RE)
build_nfa_BAR_NA(FA_Id,S,[bar|RE],N):-
    build_nfa_BAR_NA(FA_Id,S,bar(RE),N).
build_nfa_BAR_NA(FA_Id,S,bar([RE|[]]),N):-gensym(q,X),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    build_nfa_BAR(FA_Id,X,RE,N),
    retract(nfa_final(FA_Id,S)),
    retract(nfa_delta_bar(FA_Id,X,qFinBar)),
    retract(nfa_delta_bar(FA_Id,N,qFinBar)),
    assert(nfa_final(FA_Id,N)).
 
%Definizione di build_nfa_BAR_NA per RE=oneof(ATOM1,ATOM2,...,ATOMs)
build_nfa_BAR_NA(FA_Id,S,[oneof|RE],N):-
    gensym(q,X),
    assert(nfa_delta_epsilon(FA_Id,S,X)),
    build_nfa_BAR_NA(FA_Id,X,oneof(RE),N).
build_nfa_BAR_NA(FA_Id,S,oneof([RE|[]]),N):-
    gensym(q,X),
    assert(nfa_delta_epsilon(FA_Id,X,N)),
    assert(nfa_error(FA_Id,qFin)),
    build_nfa_BAR(FA_Id,S,RE,X),!.
build_nfa_BAR_NA(FA_Id,S,oneof([RE|REs]),N):-
    gensym(q,X),
    assert(nfa_delta_epsilon(FA_Id,X,N)),
    build_nfa_BAR(FA_Id,S,RE,X),
    build_nfa_BAR_NA(FA_Id,S,oneof(REs),N).
 
% PREDICATO nfa_recognize/2
% Passo un Input all'automa FA_Id e verifico che esista uno stato
% iniziale (nfa_initial)in FA_Id e mi chiedo se Input è una sequenza
% accettata (nfa_check/3)da FA_Id.
 
% ATTENZIONE!!
% Non garantiamo un risultato corretto nel caso di riconoscimento di
% automi ottenuti compilando una RE contenente la negazione bar(RE)!
% Per tutte le specifiche, visionare il file README.txt allegato,alla
% voce PREFAZIONE!
 
nfa_recognize(FA_Id,Input) :- nfa_initial(FA_Id,S),
    nfa_check(FA_Id,Input,S),
    write('The word has been accepted by the AUTOMA '),
    write(FA_Id),write('!   Well Done! :)'),!.
 
nfa_recognize(FA_Id,_) :-
    write('ERROR: The INPUT is not acceptable by the AUTOMA '),
    write(FA_Id),write('! :('),fail.
 
% PREDICATO nfa_check/3
% Verifico che nell'automa FA_Id, tramite la funzione delta classica
% (nfa_delta) o tramite funzione delta specifica bar(nfa_delta_bar), se
% consentito (nfa_illegal_delta_bar), considerando carattere per
% carattere il mio input posso arrivare ad uno stato che sia finale
% (nfa_final) e non di errore(nfa_error). Se così fosse, il mio input
% sarà accettato da FA_Id. Tutto ciò è necessario per il predicato
% nfa_recognize.
 
 
nfa_check(FA_Id,Input,Q):- nfa_delta_epsilon(FA_Id,Q,N),
    nfa_check(FA_Id,Input,N).
nfa_check(FA_Id,[I|Is],Q) :- nfa_delta(FA_Id,Q,I,N),!,nfa_check(FA_Id,Is,N).
nfa_check(FA_Id,[I|Is],Q) :- not(nfa_illegal_delta_bar(FA_Id,Q,I,_)),
    nfa_delta_bar(FA_Id,Q,N),nfa_check(FA_Id,Is,N).
nfa_check(FA_Id,[],Q) :- !,
    not(nfa_error(FA_Id, Q)),
    nfa_final(FA_Id,Q).
 
% PREDICATI nfa_clear
% Pulisco la base dati eliminando tutte le asserzioni stati iniziali,
% finali e intermedi, utilizzando il predicato retractall/1.
 
% nfa_clear/0 in cui pulisco la base dati eliminando tutti gli automi
% precedentemente definiti.
nfa_clear:- retractall(nfa_initial(_,_)),
    retractall(nfa_final(_,_)),
    retractall(nfa_error(_,_)),
    retractall(nfa_delta_epsilon(_,_,_)),
    retractall(nfa_illegal_delta_bar(_,_,_,_)),
    retractall(nfa_delta(_,_,_,_)),
    retractall(nfa_delta_bar(_,_,_)),
    write('All the AUTOMAs have been cleared!').
 
% nfa_clear_nfa/1 in cui pulisco la base dati eliminando l'automa FA_Id
% precedentemente definito.
nfa_clear_nfa(FA_Id):- retractall(nfa_initial(FA_Id,_)),
    retractall(nfa_final(FA_Id,_)),
    retractall(nfa_delta(FA_Id,_,_,_)),
    retractall(nfa_error(FA_Id,_)),
    retractall(nfa_illegal_delta_bar(FA_Id,_,_,_)),
    retractall(nfa_delta_epsilon(FA_Id,_,_)),
    retractall(nfa_delta_bar(FA_Id,_,_)),
    write('The AUTOMA '),
    write(FA_Id),
    write(' has been cleared!').
 
% PREDICATI nfa_list
% "Stampo a schermo" la definizione dell'automa, listando gli
% stati iniziali e finali, e le funzioni delta che le legano, utilizzando il
% predicato listing/1.
 
% PREDICATO nfa_list/0
% "Stampo a schermo" tutti gli stati iniziali e finali e le funzioni
% delta di  ogni automa precendentemente definito.
nfa_list:- listing(nfa_initial(_,_)),
       listing(nfa_delta(_,_,_,_)),
       listing(nfa_delta_epsilon(_,_,_)),
       listing(nfa_delta_bar(_,_,_)),
       listing(nfa_illegal_delta_bar(_,_,_,_)),
       listing(nfa_final(_,_)),
       listing(nfa_error(_,_)),
       write('All the AUTOMAs defined have been listed!').
 
% PREDICATO nfa_list/1
% "Stampo a schermo" tutti gli stati iniziali e finali e le funzioni
% delta dell' automa FA_Id precendentemente definito.
nfa_list(FA_Id):- check_ID_listing(FA_Id),
    listing(nfa_initial(FA_Id,_)),
    listing(nfa_delta(FA_Id,_,_,_)),
    listing(nfa_delta_epsilon(FA_Id,_,_)),
    listing(nfa_illegal_delta_bar(FA_Id,_,_,_)),
    listing(nfa_delta_bar(FA_Id,_,_)),
    listing(nfa_final(FA_Id,_)),
    listing(nfa_error(FA_Id,_)),
    write('The AUTOMA '),
    write(FA_Id),
    write(' has been listed!').
 
% PREDICATO check_ID_listing/1
% Controllo se esiste la definizione precedente di un automa con lo
% stesso FA_Id, per poterlo listare o, eventualmente, restituire un
% errore.
 
check_ID_listing(FA_Id) :- nfa_initial(FA_Id,_),!.
check_ID_listing(FA_Id):- write('ERROR: The AUTOMA '),write(FA_Id),
    write(' is not defined in memory!'),fail.
