#lang racket

;; Implementation of Parsec, based on Leijen and Meijer's 2001 TR
;; Parsec implements LL1 grammars
;; returns first successful parse, even for ambiguous grammars

;; add laziness

;; ----------------------------------------------------------------------------
;; Type declarations

;; An Input is a [ListOf Char]

;; [ ] in function signatures is type instantiation, not a list

;; A [Parser X] is a function: Input -> [ParseOut X]
;;   where X is the type of the result, ie a Tree

;; Parser identifiers have a "$" prefix
;; Parser generating functions typically use a "mk$" prefix

;; A [ParseOut X] is one of:
;;  -- (Consumed res:[ParseResult X])
;;  -- (Empty res:[ParseResult X])
;;     where res is a struct containing the result of parsing and remaining input
;; The Consumed case indicates input was consumed and 
;; the Empty case indicates that no input was consumed
(struct Consumed (res) #:transparent)
(struct Empty (res) #:transparent)

;; A [ParseResult X] is one of:
;;  -- (ParseResult x:X next:Input)
;;     where: x is the result, with type X
;;            next is the remaining input
;;  -- 'Error
;; (ParseResult is equiv to the [Reply X] datatype in the Parsec paper,
;;  where the non-error case is equiv to the Ok constructor)
(struct ParseResult (x next) #:transparent)




;; ----------------------------------------------------------------------------
;; Helper fns

;; str-cons :: Char [ListOf Char] -> String
(define (str-cons c cs) (string-append (string c) cs))
(define (empty-string? s) (string=? "" s))

;; ----------------------------------------------------------------------------
;; monadic syntax for combining parsers
;; (~ x <- p1
;;    y <- p2
;;    ...
;;    f x y ...)
;;     expands to
;; (>>= p1 (λ (x) (>>= p2 (λ (y) (>>= ... (mk$nop (f x y ...)))))))
;;
;; currently doesnt handle:
;;  - guards 
;;  - "any" (ie: '_' identifier -- it'll work but if _ is used in result, 
;;                                 then things could go wrong)
(define-syntax (~ stx)
  (syntax-case stx (<-)
    [(_ e) #'(mk$nop e)]
    [(_ x <- p rest ...)
     #'(>>= p (match-lambda [x (~ rest ...)]))]))



;; ----------------------------------------------------------------------------
;; basic parser combinators

;; mk$nop :: a -> Parser a
;; makes a Parser that consumes no input and returns x as result (ie, a no-op)
;; (equiv to result or return Parser in papers)
(define (mk$nop x) (λ (inp) (Empty (ParseResult x inp))))

;; mk$sat :: (Char -> Bool) -> Parser Char
;; makes a Parser that consumes a char if given predicate is satisfied, 
;;   else fail
;; (equiv to sat Parser from paper)
(define (mk$sat p?)
  (λ (inp)
    (cond [(empty-string? inp) (Empty 'Error)]
          [else (let ([c (string-ref inp 0)])
                  (if (p? c)
                      (let ([cs (substring inp 1)])
                        (Consumed (ParseResult c cs)))
                      (Empty 'Error)))])))

;; >>= :: Parser a -> (a -> Parser b) -> Parser b
;; bind operator
(define (>>= $p f) 
  (λ (inp) 
    (match ($p inp)
      [(Empty (ParseResult x _)) ((f x) inp)]
      [(Empty 'Error) (Empty 'Error)]
      [(Consumed res1)
       (Consumed
        (match res1
          [(ParseResult x rest)
           (match ((f x) rest)
             [(Consumed res2) res2]
             [(Empty res2) res2])]
          [err err]))])))

  
;; <or> :: Parser a -> Parser a -> Parser a
;; choice combinator (ie "plus" or <|> or ++)
(define (<or> p q) 
  (λ (inp) 
    (match (p inp)
      [(Empty 'Error) (q inp)]
      [(Empty res)
       (match (q inp)
         [(Empty _) (Empty res)]
         [consumed consumed])]
      [consumed consumed])))

;; try :: Parser a -> Parser a
#;(define (try $p)
  (λ (inp)
    (match ($p inp)
      [(ParseResult #t 'Error _) (ParseResult #f 'Error inp)]
      [other other])))
  
  
;; ----------------------------------------------------------------------------
;; derived parser combinators


;; $fail :: Parser a
;; (equiv to zero Parser in paper)
(define ($fail inp) null)

;; $char :: Parser Char
;; (equiv to item in paper)
;; parses one char of non-empty input, or fail
(define ($char inp)
  (if (empty-string? inp)
      (Empty 'Error)
      (Consumed (ParseResult (string-ref inp 0) (substring inp 1)))))

;; ----------------------------
;; combinators derived from sat
  
;; mk$char :: Char -> Parser Char
(define (mk$char c1) (mk$sat (λ (c2) (eq? c1 c2))))

;; $digit, $lower, $upper :: Parser Char
;; parsers one number, lowercase, or uppercase char
(define $digit (mk$sat (λ (x) (and (char<=? #\0 x) (char<=? x #\9)))))
(define $lower (mk$sat (λ (x) (and (char<=? #\a x) (char<=? x #\z)))))
(define $upper (mk$sat (λ (x) (and (char<=? #\A x) (char<=? x #\Z)))))

 
;; ------------------------------
;; combinators derived from <or>

;; $letter,$alphanum :: Parser Char
;; parses any one letter or alphanumeric char
(define $letter ($lower . <or> . $upper))
(define $alphanum ($letter . <or> . $digit))

;; $word :: Parser String
(define $word-no-do
  (let ([$neWord
         (>>= 
          $letter
          (λ (x)
            (>>= 
             $word
             (λ (xs)
               (mk$nop (str-cons x xs))))))])
    ($neWord . <or> . (mk$nop ""))))

(define $word
  (let ([$neWord (~ x  <- $letter
                    xs <- $word
                    (string-append (string x) xs))])
    ($neWord . <or> . (mk$nop ""))))



;; mk$string :: String -> Parser String
;; makes a Parser that accepts the given string
(define (mk$string s)
  (if (string=? s "")
      (mk$nop "")
      (~ c  <- (mk$char  (string-ref s 0))
         cs <- (mk$string (substring s 1))
         (str-cons c cs))))

;; <*> :: Parser a -> Parser [a]
;; kleene star
;; (equiv to "many" combinator in paper)
(define (<*> p)
  ((~ x <- p
      xs <- (<*> p)
      (cons x xs))
   . <or> .
   (mk$nop null)))

   
;; [Parser X]  -> [Parser [ListOf X]]
;; (equiv to many1 in paper)
;; at least one, then kleene star
(define (<+> p)
  (~ x  <- p
     xs <- ((<+> p) . <or> . (mk$nop null))
     (cons x xs)))

;; $ident :: Parser String
;; parses a Haskell identifier (begins with lowercase)
(define $ident
  (<+> (($letter . <or> . $digit) . <or> . (mk$char #\_))))

;; $nat :: Parser Int
#;(define $nat
  (let* ([op (λ (y x) (+ (* 10 x) y))]
         [eval (λ (xs) 
                 (let
                     ([lst (map (λ (x) (- (char->integer x) (char->integer #\0))) xs)])
                   (foldl op (first lst) (rest lst))))])
    (~ xs <- (<+> $digit)
       (eval xs))))
; using chainl1 from sec 4.3
(define ($nat inp)
  (let ([op (λ (y x) (+ (* 10 x) y))])
    ((chainl1 
      (~ x <- $digit
         (- (char->integer x) (char->integer #\0)))
      (mk$nop op))
     inp)))

;; $int :: Parser Int
(define $int
  (let ([$op ((~ tmp <- (mk$char #\-)
                 -)
              . <or> .
              (mk$nop (λ (x) x)))])
  (~ f <- $op
     n <- $nat
     (f n))))

;; $ints :: Parser [ListOf Int]
(define $ints 
  (~ _  <- (mk$char #\[)
     n  <- $int
     ns <- (<*> (~ _ <- (mk$char #\,)
                   x <- $int
                   x))
     _ <- (mk$char #\])
     (cons n ns)))

;; sepby1 :: Parser a -> Parser a -> Parser [ListOf a]
(define (sepby1 p sep)
  (~ x <- p
     xs <- (<*> (~ _ <- sep
                   y <- p
                   y))
     (cons x xs)))

;; $ints-sepby1 :: Parser [ListOf Int]
(define $ints-sepby1
  (~ _ <- (mk$char #\[)
     ns <- (sepby1 $int (mk$char #\,))
     _ <- (mk$char #\])
     ns))

;; bracket :: Parser a -> Parser b -> Parser c -> Parser b
;; brackets Parser b with Parser a and c (latter 2 results are ignored)
(define (mk$bracket open p close)
  (~ _ <- open
     x <- p
     _ <- close
     x))

;; $ints-sepby1-bracket :: Parser [ListOf Int]
(define $ints-sepby1-bracket
  (mk$bracket (mk$char #\[)
              (sepby1 $int (mk$char #\,))
              (mk$char #\])))

;; $sepby :: Parser a -> Parser b -> Parser [ListOf a]
(define (sepby p sep)
  ((sepby1 p sep)
   . <or> .
   (mk$nop null)))

;; $expr :: Parser Int
;; $addop :: Parser (Int -> Int -> Int)
;; $factor :: Parser Int

; left recursive
#;(define $expr
  ((~ x <- $expr
      f <- $addop
      y <- $factor
      (f x y))
   . <or> .
   $factor))
; right recursive
; cant just do (define $expr ...), get $factor not defined error
; must eta expand to (define ($expr inp) ...)
#;(define ($expr inp)
  ((~ x  <- $factor
     fys <- (<*> (~ f <- $addop
                    y <- $factor
                    (cons f y)))
     (foldl (match-lambda** [((cons f y) x) (f x y)]) x fys))
   inp))
#;(define (chainl1 p op)
  (~ x   <- p
     fys <- (<*> (~ f <- op
                    y <- p
                    (cons f y)))
     (foldl (match-lambda** [((cons f y) x) (f x y)]) x fys)))
; avoids creating intermediate list
(define (chainl1 p op)
  (define (f x)
    ((op . >>= . (λ (g)
     (p  . >>= . (λ (y)
      (f (g x y))))))
     . <or> .
     (mk$nop x)))
  (p . >>= . f))
(define ($expr inp) ((chainl1 $factor $addop) inp))
#;(define $addop
  ((~ _ <- (mk$char #\+)
      +)
   . <or> .
   (~ _ <- (mk$char #\-)
      -)))
(define $factor
  ($nat
   . <or> .
   (mk$bracket (mk$char #\() $expr (mk$char #\)))))

;; ops :: [(cons Parser a b)] -> Parser b
(define (ops xs)
  (let ([ps (map (match-lambda [(cons p op) (~ _ <- p op)]) xs)])
    (foldr <or> (first ps) (rest ps))))

(define $addop
  (ops (list (cons (mk$char #\+) +)
             (cons (mk$char #\-) -))))

;; chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
(define (chainr1 p op)
  (p . >>= . (λ (x)
  ((~ f <- op
      y <- (chainr1 p op)
      (f x y))
   . <or> .
   (mk$nop x)))))