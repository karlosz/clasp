(in-package #:clasp-cleavir)

;;;; Functions to facilitate conversion into the form of SSA needed by
;;;; translation into LAP code.

(defun map-data (function initial-instruction)
  (let ((seen (make-hash-table :test #'eq)))
    (cleavir-ir:map-instructions-arbitrary-order
     (lambda (instruction)
       (dolist (input (cleavir-ir:inputs instruction))
         (unless (nth-value 1 (gethash input seen))
           (funcall function input)
           (setf (gethash input seen) t)))
       (dolist (output (cleavir-ir:outputs instruction))
         (unless (nth-value 1 (gethash output seen))
           (funcall function output)
           (setf (gethash output seen) t))))
     initial-instruction)))

(defun data-of-type (initial-instruction type)
  (let (data)
    (map-data (lambda (datum)
                (when (typep datum type)
                  (push datum data)))
              initial-instruction)
    data))

;;; Return a list of variables defined in a basic block
(defun basic-block-definitions (basic-block)
  (let (variables)
    (cleavir-basic-blocks:map-basic-block-instructions
     (lambda (instruction)
       (dolist (output (cleavir-ir:outputs instruction))
         (when (typep output 'cleavir-ir:lexical-location)
           (pushnew output variables))))
     basic-block)
    variables))

(defun starting-basic-blocks (basic-blocks)
  ;; we define a starting basic block as the one that starts with the
  ;; owning instruction
  (remove-if-not (lambda (basic-block)
                   (eq (cleavir-basic-blocks:first-instruction basic-block)
                       (cleavir-basic-blocks:owner basic-blocK)))
                 basic-blocks))

;; algorithm adapted from appel based on dominance frontiers
;; BEWARE: the pseudocode in appel has some typos/is wrong
(defun place-phi-functions (variables basic-blocks)
  (let ((definition-sites (make-hash-table :test #'eq))
        (phi-sites (make-hash-table :test #'eq)))
    (dolist (basic-block basic-blocks)
      (dolist (variable (basic-block-definitions basic-block))
        (pushnew basic-block (gethash variable definition-sites))))
    (dolist (starting-basic-block (starting-basic-blocks basic-blocks))
      (let ((dominance-frontiers
              (cleavir-dominance:dominance-frontiers starting-basic-block
                                                     #'cleavir-basic-blocks:successors)))
        (dolist (variable variables)
          (let ((worklist (gethash variable definition-sites)))
            (loop
              (when (null worklist) (return))
              (let ((basic-block (pop worklist)))
                (dolist (y (cleavir-dominance:dominance-frontier dominance-frontiers basic-block))
                  (unless (member y (gethash variable phi-sites))
                    (let* ((cleavir-ir:*policy* (cleavir-ir:policy (cleavir-basic-blocks:first-instruction y)))
                           (cleavir-ir:*dynamic-environment* (cleavir-ir:dynamic-environment (cleavir-basic-blocks:first-instruction y)))
                           (phi (cleavir-ir:make-phi-instruction
                                 (make-list (length (cleavir-basic-blocks:predecessors y))
                                            :initial-element variable)
                                 variable
                                 ;; if we have this set to (first y) then y has a
                                 ;; circular reference to itself when we insert
                                 ;; instruction before
                                 (cleavir-ir:make-nop-instruction nil))))
                      (cleavir-ir:insert-instruction-before phi (cleavir-basic-blocks:first-instruction y))
                      ;; update the basic block as well
                      (setf (cleavir-basic-blocks:first-instruction y) phi)
                      (pushnew y (gethash variable phi-sites))
                      (unless (member y (gethash variable definition-sites))
                        (pushnew y worklist)))))))))))))

(defun delete-phi (instruction)
  (assert (= (length (cleavir-ir:successors instruction)) 1))
  (let ((successor (first (cleavir-ir:successors instruction)))
        (predecessors (cleavir-ir:predecessors instruction)))
    (if (and (typep instruction 'cleavir-ir:phi-instruction)
             (rest predecessors)
             (typep successor 'cleavir-ir:phi-instruction)
             (rest (cleavir-ir:predecessors successor)))
        (change-class instruction 'cleavir-ir:nop-instruction
                      :inputs '()
                      :outputs '())
        (cleavir-ir:delete-instruction instruction))))

;;; Return the predecessors of the top most phi node of the cluster
(defun phi-predecessors (instruction)
  (do ((phi instruction (first (cleavir-ir:predecessors phi))))
      ((or (rest (cleavir-ir:predecessors phi))
           (not (typep (first (cleavir-ir:predecessors phi))
                       'cleavir-ir:phi-instruction)))
       (cleavir-ir:predecessors phi))
    (assert (typep phi 'cleavir-ir:phi-instruction))))

(defun map-phi-cluster (function top-phi)
  (do ((phi top-phi (first (cleavir-ir:successors phi))))
      ((or (and (not (eq phi top-phi))
                (rest (cleavir-ir:predecessors phi)))
           (not (typep phi 'cleavir-ir:phi-instruction))))
    (funcall function phi)))

;; rename variables after phi instructions have been inserted
(defun ssa-rename-variables (variables basic-blocks)
  (let ((stacks (make-hash-table :test #'eq)))
    (dolist (variable variables)
      (push (cleavir-ir:make-lexical-location (gensym "SSA"))
            (gethash variable stacks)))
    (labels ((rename (basic-block dominance-tree children &aux old-defs)
               (cleavir-basic-blocks:map-basic-block-instructions
                (lambda (i)
                  (unless (typep i 'cleavir-ir:phi-instruction)
                    ;; substitute each use
                    (dolist (input (cleavir-ir:inputs i))
                      (when (typep input 'cleavir-ir:lexical-location)
                        (setf (cleavir-ir:inputs i)
                              (substitute (first (gethash input stacks))
                                          input
                                          (cleavir-ir:inputs i))))))
                  (dolist (output (cleavir-ir:outputs i))
                    (when (typep output 'cleavir-ir:lexical-location)
                      (let ((new (cleavir-ir:make-lexical-location (gensym "SSA"))))
                        (push output old-defs)
                        (push new (gethash output stacks))
                        ;; instructions can share their output and
                        ;; input lists!
                        (setf (cleavir-ir:outputs i)
                              (substitute new
                                          output
                                          (cleavir-ir:outputs i)))))))
                basic-block)
               (dolist (y (cleavir-basic-blocks:successors basic-block))
                 (let ((j (position (cleavir-basic-blocks:last-instruction basic-block)
                                    (cleavir-ir:predecessors (cleavir-basic-blocks:first-instruction y)))))
                   (cleavir-basic-blocks:map-basic-block-instructions
                    (lambda (i)
                      (when (typep i 'cleavir-ir:phi-instruction)
                        (let ((variable (nth j (cleavir-ir:inputs i))))
                          (setf (nth j (cleavir-ir:inputs i))
                                (first (gethash variable stacks))))))
                    y)))
               (dolist (child (gethash basic-block children))
                 (rename child dominance-tree children))
               (dolist (old-def old-defs)
                 (when (typep old-def 'cleavir-ir:lexical-location)
                   (pop (gethash old-def stacks))))))
      (dolist (starting-basic-block (starting-basic-blocks basic-blocks))
        (let ((dominance-tree (cleavir-dominance:dominance-tree
                               starting-basic-block
                               #'cleavir-basic-blocks:successors)))
          (rename starting-basic-block
                  dominance-tree
                  (cleavir-dominance:children dominance-tree)))))))

(defun convert-ssa-form (enter-instruction)
  (let ((variables (data-of-type enter-instruction 'cleavir-ir:lexical-location))
        (basic-blocks (cleavir-basic-blocks:basic-blocks enter-instruction)))
    (place-phi-functions variables basic-blocks)
    (ssa-rename-variables variables basic-blocks))
  (cleavir-ir:reinitialize-data enter-instruction))

;; Sometimes, we get cycles of phi nodes. Aggressively eliminate them.
;; You must do this after copy propogation for it to catch everything.
(defun aggressive-dead-phi-elimination (initial-instruction)
  (let* ((phi-nodes (cleavir-ir:instructions-of-type initial-instruction
                                                    'cleavir-ir:phi-instruction))
         (worklist (copy-list phi-nodes))
         live-phi)
    (loop (when (null worklist) (return))
          (let ((phi-node (pop worklist)))
            (when (some (lambda (use)
                          (or (not (typep use 'cleavir-ir:phi-instruction))
                              (member use live-phi)))
                        (cleavir-ir:using-instructions (first (cleavir-ir:outputs phi-node))))
              (unless (member phi-node live-phi)
                (push phi-node live-phi)
                (dolist (input (cleavir-ir:inputs phi-node))
                  (dolist (def (cleavir-ir:defining-instructions input))
                    (when (typep def 'cleavir-ir:phi-instruction)
                      (pushnew def worklist))))))))
    (dolist (phi-node (set-difference phi-nodes live-phi))
      (cleavir-ir:delete-instruction phi-node)))
  (cleavir-ir:reinitialize-data initial-instruction))

(defun basic-block-phi-functions (basic-block)
  (let (phis)
    (block nil
      (cleavir-basic-blocks:map-basic-block-instructions
       (lambda (instruction)
         (unless (typep instruction 'cleavir-ir:phi-instruction)
           (return))
         (push instruction phis))
       basic-block))
    (nreverse phis)))

(defun count-basic-block-phi-functions (basic-block)
  (let ((count 0))
    (block nil
      (cleavir-basic-blocks:map-basic-block-instructions
       (lambda (instruction)
         (unless (typep instruction 'cleavir-ir:phi-instruction)
           (return))
         (incf count))
       basic-block))
    count))

(defun phi-function-position (phi-function basic-block)
  (let ((pos 0))
    (cleavir-basic-blocks:map-basic-block-instructions
     (lambda (instruction)
       (unless (typep instruction 'cleavir-ir:phi-instruction)
         (error "no such phi function in block"))
       (when (eq phi-function instruction)
         (return-from phi-function-position pos))
       (incf pos))
     basic-block)))

(defun last-phi-or-none-in-cluster (start)
  (do ((instruction start (first (cleavir-ir:successors instruction)))
       (last nil instruction))
      ((not (typep instruction 'cleavir-ir:phi-instruction))
       (or last start))))
