; lambda calculus data structure from Part 1:

; Constructors:
(define make-lambda-abs
  (lambda (var exp)
    (list 'lambda (list var) exp)))

(define make-lambda-app
  (lambda (func inp)
    (list func inp)))

; Selectors:
(define abs-var
  (lambda (expr)
    (cadr expr)))

(define abs-e
  (lambda (expr)
    (caddr expr)))

(define app-e1
  (lambda (expr)
    (car expr)))

(define app-e2
  (lambda (expr)
    (cadr expr)))

; Classifiers:
(define variable?
  (lambda (expr)
    (and (not (null? expr))
         (not (pair? expr)))))

(define lambda-abs?
  (lambda (expr)
    (and (not (null? expr))
         (eq? (car expr) 'lambda)
         (variable? (car (abs-var expr)))
         (not (null? (abs-e expr))))))

(define lambda-app?
  (lambda (expr)
    (and (not (null? expr))
         (not (variable? expr))
         (not (lambda-abs? expr))
         (not (null? (car expr)))
         (not (null? (cdr expr))))))

; elem and remove-dup helper functions from Part 1:

(define (elem e l)
  (define (accumulate-left op init seq)
    (define (iter acc rest)
      (if (null? rest)
          acc
          (iter (op acc (car rest))
                (cdr rest))))
    (iter init seq))
  
  (accumulate-left
   (lambda (acc first)
     (or acc (eq? first e)))
   #f
   l))

(define remove-dup
  (lambda (lst)
    (cond ((null? lst) '())
          ((elem (car lst) (cdr lst)) (remove-dup (cdr lst)))
          (else (cons (car lst) (remove-dup (cdr lst)))))))

; free-vars, bound-vars, and all-ids from Part 1:

(define free-vars
  (lambda (E)
    (remove-dup (list-free-vars E '() '()))))

(define list-free-vars
  (lambda (E lst y)
    (cond ((variable? E) (cond ((not (elem E y)) (append (list E) lst)) (else lst)))
          ((lambda-app? E) (append (list-free-vars (app-e1 E) lst y) (list-free-vars (app-e2 E) lst y)))
          ((lambda-abs? E) (list-free-vars (abs-e E) lst (append (abs-var E) y))))))

(define bound-vars
  (lambda (E)
    (remove-dup (list-bound-vars E '() '()))))

(define list-bound-vars
  (lambda (E lst y)
    (cond ((variable? E) (cond ((elem E y) (append (list E) lst)) (else lst)))
          ((lambda-app? E) (append (list-bound-vars (app-e1 E) lst y) (list-bound-vars (app-e2 E) lst y)))
          ((lambda-abs? E) (list-bound-vars (abs-e E) lst (append (abs-var E) y))))))

(define all-ids
  (lambda (E)
    (remove-dup (list-all-ids E '()))))

(define list-all-ids
  (lambda (E lst)
    (cond ((variable? E) (append (list E) lst))
          ((lambda-app? E) (append (list-all-ids (app-e1 E) lst) (list-all-ids (app-e2 E) lst)))
          ((lambda-abs? E) (append (abs-var E) (list-all-ids (abs-e E) lst))))))

; new-var helper function:
; Note that element-of was changed to elem since that does what element-of is supposed to do.

(define (new-var lambda-exp str)
  (define old-vars (all-ids lambda-exp))
  (define (iter n)
    (let ((new (string->symbol (string-append str (number->string n)))))
      (cond ((not (elem new old-vars)) new)
            (else (iter (+ n 1))))))
  (iter 0))

; Part 2:
; Note: Due to how the data structure is defined in Part 1, instead of e1, e2, and v, subst will take l1, l2, and v to avoid confusion.

; Design process of helper functions:

;; The plan is to perform the substitution of the variables that would result in capturing before replacing v with l2. The design idea is
;; to create a function that checks if an id in l2 occurs in l1. For this function to only change variables that has to be changed (and by consequence avoid
;; the creation of new unnecessary variables), a helper function that performs that check needs to be made. That helper function will be called needs-change?

; Designing needs-change?:

;; A variable in l1 that is an element in l2 needs to be changed (in other words, needs-change? returns true) iff:
;; 1. When l1' = (lambda (x) e)
;;    a. x must not be equal to v.
;;    b. If x = l2-var, then v must occur free in e.
;;    c. If x =/= l2-var, then l2-var must meet the condition in e.
;; 2. If l1''' = (e1 e2), then l2-var needs to meet the criteria in either e1 or e2.

;; Since this is a recursive definition, it needs to be proven based on the complexity of the lambda calculus expression passed onto needs-change?
;; For reference, here is the BNF: <expr> ::= <variable> | (lambda ( <variable> ) <expr> )  |  ( <expr> <expr> )

; Proof of needs-change?

;; Precondition: l1 is a valid <expr>, l2-var is a <variable> in l2, and v is a <variable>.
;; Note: The definition of <expr>'s do not allow for empty sets so it should go without saying that l1 cannot be null.
;; Postcondition: needs-change? returns true or false depending on whether l1 meeds the conditions listed above.

;; Base case: l1 is a variable. If l1 is a variable then by definition it is not an abstraction or an application, therefore needs-change? returns false.

;; Inductive hypothesis: If l1 is a lambda abstraction, then it takes on the form (lambda ( <variable> ) <expr> ). That means that the <variable> inside l1
;; can be compared to v and l2-var. If the <variable> is equal to v, needs-change? returns false. If the <variable> is equal to l2-var, elem will check 
;; if v occurs free in <expr>. Otherwise, needs-change? will check whether l2-var meets the criteria in <expr>. If l1 is an application,
;; needs-change? will check if l2-var meets the criteria in either <expr>.

;; Inductive step: An <expr> can either be an abstraction, application, or variable. That means that any <expr> in the IH will be one of these
;; three forms. Which then means that it is either the IH, where it can be checked whether l2-var meets the criteria, or it is a variable, in which it will return
;; false as given by the base case. That means that for any lambda abstraction, it will eventually return either true or false and for any lambda application,
;; it will return the result of performing logical or on two boolean statements. Thanks to the BNF, this will always hold for any <expr> regardless of its
;; complexity assuming the preconditions are met.

;; Termination condition: Once needs-change? goes through the entirety of l1, it will return true or false.
;; Does it terminate? Assuming the recursive calls work, it will terminate once it figures out whether needs-change? is true or false for any l1.

; needs-change?:
(define needs-change?
  (lambda (l1 l2-var v)
    (cond ((variable? l1) #f)
          ((lambda-abs? l1) (cond ((eq? (car (abs-var l1)) v) #f)
                                  ((and (eq? (car (abs-var l1)) l2-var) (elem v (free-vars (abs-e l1))) #t))
                                  (else (needs-change? (abs-e l1) l2-var v))))
          ((lambda-app? l1) (or (needs-change? (app-e1 l1) l2-var v) (needs-change? (app-e2 l1) l2-var v))))))

; Designing swap-var:

;; Once needs-change? returns true, then the function that replaces the variable, old-var, with a new one, new-var, can be called.
;; Not every instance of the variable has to change however. The a variable will be replaced iff:

;; 1. If l1 is equal to old-var, it must be bound to some abstraction l1' where v occurs free in l1'. A boolean will be used for this purpose.
;; 2. If l1' is an abstraction whose <variable> is equal to old-var, v must occur free in its <expr>.  
;; 2. If l1'' is an application, then the variable will be changed for either <expr> if the condition is met.

;; This is also a recursive definition on the structure of l1. Therefore, it needs to be proven.

; Proof of swap-var:

;; Precondition: l1 is a valid <expr>, v is a <variable>, old-var is a <variable> in l2, new-var is a <variable> not in l1, replace? is a boolean set to false.
;; Postcondition: swap-var returns a logically equivalent <expr> to l1 where any old-var that will cause capturing has been changed to new-var.

;; Base case: l1 is a variable. If l1 is a variable equal to old-var and replace? is true, new-var will be returned. Otherwise, l1 will be returned.

;; Inductive hypothesis: If l1 is a lambda abstraction, then it takes on the form (lambda ( <variable> ) <expr> ). That means that the <variable> inside l1
;; can be compared to old-var. If the <variable> is not equal to old-var, replace? remains the same. Otherwise, it will be checked
;; if v occurs free in the <expr> of l1. If true, replace? will be set to true and the <variable> will be changed to new-var.
;; If not, replace? will be set to false. swap-var will then continue by looking at <expr>. If l1 is an application, then it will look at both <expr>'s to
;; look for any valid variable changes.

;; Inductive step: An <expr> can either be an abstraction, application, or variable. That means that any <expr> in the IH will be one of these
;; three forms. Which then means that it is either the IH, where the checks mentioned in the IH will be performed, or it is a variable, where the variable
;; will be swapped with new-var if replaced? is true or remain the same otherwise. That means that for any lambda abstraction or application, it will eventually
;; return a logically equivalent statement to l1 with the capturing variables changed. Thanks to the BNF, this will always hold for any <expr> regardless of its
;; complexity assuming the preconditions are met.

;; Termination condition: Once swap-var goes through the entirety of l1, it will return the modified statement.
;; Does it terminate? Assuming the recursive calls work, it will terminate once it goes through the entire expression and its sub-expressions.

; swap-var:
(define swap-var
  (lambda (l1 v old-var new-var replace?)
    (cond ((variable? l1) (cond ((and replace? (eq? l1 old-var)) new-var)
                                (else l1)))
          ((lambda-abs? l1) (cond ((not (eq? (car (abs-var l1)) old-var)) (make-lambda-abs (car (abs-var l1)) (swap-var (abs-e l1) v old-var new-var replace?)))
                                  ((elem v (free-vars (abs-e l1))) (make-lambda-abs new-var (swap-var (abs-e l1) v old-var new-var #t)))
                                  (else (make-lambda-abs old-var (swap-var (abs-e l1) v old-var new-var #f)))))                      
          ((lambda-app? l1) (make-lambda-app (swap-var (app-e1 l1) v old-var new-var replace?) (swap-var (app-e2 l1) v old-var new-var replace?))))))

; Designing subst-capture:

;; Now that there are functions that checks for capturing variables and replaces them appropriately, a function designed to perform these tasks for all ids
;; in l2 can be designed. It works as follows:

;; 1. Check if l2-vars is empty, meaning it has no ids. In this case, return l1 since it causes no conflicts.
;; 2. Check if the first id of l2-vars will result in capturing once the subsitution occurs and is not equal to v.
;;    If so, call swap-var to mend this issue. Move onto the next id.
;; 3. Otherwise, move onto the next id.

;; In this case, assuming l2-vars is a proper list of ids, inducting on l2-vars' length is possible as l2-vars would then only contain ids which is a <variable>.

; Proof of subst-capture:

;; Precondition: l1 is a valid <expr>, l2-vars is a valid list of l2's ids, v is a variable.
;; Postcondition: Returns a list logically equivalent to l1 where ALL variables that would have caused capturing when (subst l1 l2 v) is called have been replaced.

;; Base case: List has a length of 0. Return e1.

;; Inductive Hypothesis: For some list with length k, the first id will be processed and if it has been determined that l1 needs to be modified, swap-var
;; will be called. Otherwise leave l1 as is. subst-capture will cdr down the list until the next list has a length of 0 which is the base case.

;; Inductive Step: For some list with length k+1, the first id will be processed and modify l1 if appropriate. The next step, which involves the cdr of the list,
;; will have a length of k, which is the inductive hypothesis. The IH will reach the base case eventually so therefore the IS will as well.

;; Termnation condition: Once the end of the list has been reached the function will terminate.
;; Does it terminate? Given the nature of cdr, assuming the recursive calls work, the function will always reach the end of any list.

; subst-capture:
(define subst-capture
  (lambda (l1 l2-vars v)
    (cond ((null? l2-vars) l1)
          ((and (not (eq? v (car l2-vars))) (needs-change? l1 (car l2-vars) v)) (subst-capture (swap-var l1 v (car l2-vars) (new-var l1 "x") #f) (cdr l2-vars) v))
          (else (subst-capture l1 (cdr l2-vars) v)))))

; Designing subst-replace-v:

;; Finally, all capturing variables have been changed. Now, v can be safely replaced by l2. All subst-replace-v has to do is find
;; free occurrences of v and replace it with l2.

;; Proof of subst-replace-v:

;; Precondition: l1 and l2 are valid <expr>'s, v is a <variable>, and y is an empty list.
;; Postcondition: Returns a lambda calculus expression logically equivalent to l1 where all free instaces of v have been replaced by l2.

;; Base case: k is a variable. If k is free and equal to v then it gets replaced by l2. Otherwise it remains the same.

;; Inductive Hypothesis: If k is some abstraction lx.E, then any free occurrences of v in E will be replaced by l2.
;; If k is an abstraction EF, then any free occurrences of v in either E or F will be replaced by l2.

;; Inductive Step: For any valid <expr>, it can either be an abstraction, application, or variable. If it is a variable, then this is the base case.
;; If it is an abstraction or an application, the <expr> will perform a valid substitution thanks to the IH. On more complicated
;; <expr>'s, the components of that <expr> are also <expr>'s which means they work due to the IH and the base case.

;; Termination condition: Once the entire expression has been checked, assuming the precondition has been met, the program will terminate.
;; Does it terminate? Assuming the recursive calls work, the nature of cdr plus the BNF of <expr> shows that it will terminate.

(define subst-replace-v
  (lambda (l1 l2 v y)
    (cond ((variable? l1) (cond ((and (eq? l1 v) (not (elem v y))) l2) (else l1)))
          ((lambda-abs? l1) (make-lambda-abs (car (abs-var l1)) (subst-replace-v (abs-e l1) l2 v (append (abs-var l1) y))))
          ((lambda-app? l1) (make-lambda-app (subst-replace-v (app-e1 l1) l2 v y) (subst-replace-v (app-e2 l1) l2 v y))))))

; Designing subst:

;; Now that all the steps to perform subst have been coded, it's time to design subst. The intended flowchart of subst is as follows:

;; check if a new variable needs to be made -> make the new variable -> switch the old variables with the
;; new one if necessary -> do this for all variables in l2 -> substitute all free occurrences of v with l2

;; Proof of subst:

;; Precondition: l1 and l2 are valid <expr>'s and v is a <variable>.
;; Postcondition: Returns a logically equivalent lambda calculus expression to l1. The expression has all free instances of v replaced by l2 and
;; all capturing variables renamed.

;; There is no recursion here so the proof consists of making sure the flowchart is met for any valid l1. Thankfully,
;; every function so far has been proved, except for new-var. So in order to prove correctness for subst, the outputs
;; of the function at a certain step must help the function in the next step to produce the correct output.
;; Finally, the last function must meet the postcondition of subst for any l1.

;; needs-change? returns a boolean that lets the rest of the functions run if true ->
;; new-var returns a new variable for swap-var to replace ->
;; swap-var changes instances of the old variable that cause capturing to the one returned by new-var ->
;; subst-capture does this for every id in l2 ->
;; subst-replace-v replaces all free occurrences of v in l1 to l2

;; subst-replace-v returns an <expr> where all free instances of v have been replaced by l2 which meets part of the postcondition for subst.
;; However, as shown by the diagram, the lambda expression used in this function came from subst-capture, which replaced all variables
;; that would have caused capturing. That means that the expression returned by subst-replace-v actually meets both postconditions of subst.
;; Therefore, subst is correct.

;; Termination condition: Once subst-replace-v is done, it will return a list and the program terminates.
;; Does it terminate? All functions inside of subst terminate and it has been proven that the flowchart works seamlessly so, assuming
;; the precondition is met, subst will terminate.

(define subst
  (lambda (l1 l2 v)
    (subst-replace-v (subst-capture l1 (all-ids l2) v) l2 v '())))

; Test Code:

(subst '(lambda (x) x) '(x y) 'x)
;;returns (lambda (x) x) -- no free occurrence of x in the first argument

(subst '(lambda (x) (x y)) '(x y) 'x)
;;gives (lambda (x) (x y)) -- no free occurrence of x in the first argument

(subst '(lambda (x) (x y)) '(x y) 'y)
;;gives (lambda (x0) (x0 (x y))) -- avoiding capture of x

(subst '(lambda (x) (x (y (lambda (x) (x z))))) '(x y) 'y)
;; gives (lambda (x0) (x0 ((x y) (lambda (x) (x z)))))

(subst '(lambda (x) (x (y (lambda (x) (x y))))) '(x y) 'y)
;; gives (lambda (x0) (x0 ((x y) (lambda (x0) (x0 (x y))))))
       
(subst '(lambda (x) (x (y (lambda (y) (x (lambda (z) (x (y z)))))))) '(x (y z)) 'y)
;; gives (lambda (x0) (x0 ((x (y z)) (lambda (y) (x0 (lambda (z) (x0 (y z))))))))

(subst '(lambda (x) (x (w (lambda (y) (x (w (lambda (z) (x (y w))))))))) '(x (y z)) 'w)
;; gives (lambda (x0) (x0 ((x (y z)) (lambda (x1) (x0 ((x (y z)) (lambda (x2) (x0 (x1 (x (y z)))))))))))

(subst '((lambda (x) (x y)) (lambda (y) (x y))) 'z 'x)
;; gives ((lambda (x) (x y)) (lambda (y) (z y)))

; Code borrowed from:
; lecture10.scm - elem and accumulate-left

; Texts used for improving understanding of capturing and A-Substitution:
; https://plato.stanford.edu/entries/lambda-calculus/
; http://www.cs.unc.edu/~stotts/723/Lambda/scheme.html
; http://www.cs.unc.edu/~stotts/723/Lambda/overview.html
; https://personal.utdallas.edu/~gupta/courses/apl/lambda.pdf