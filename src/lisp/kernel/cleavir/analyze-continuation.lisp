;; Does this catch create a continuation that escapes into the harsh,
;; real world?
(defclass escape-catch-instruction (cleavir-ir:catch-instruction) ())

(defmethod cleavir-ir-graphviz:label ((instruction escape-catch-instruction)) "escape catch")

(defun analyze-catches (initial-instruction)
  ;; We are going to check for whether encloses escape, so copy propagate.
  (dolist (enclose (cleavir-ir:instructions-of-type initial-instruction 'cleavir-ir:enclose-instruction))
    (cleavir-partial-inlining::copy-propagate-1 (first (cleavir-ir:outputs enclose))))
  (let ((function-dag (cleavir-hir-transformations:build-function-dag initial-instruction))
        (ownership (cleavir-hir-transformations:compute-instruction-owners initial-instruction))
        (catches (cleavir-ir:instructions-of-type initial-instruction 'cleavir-ir:catch-instruction)))
    (dolist (catch catches)
      (analyze-catch catch function-dag ownership))))

(defun call-position-p (fun user)
  (and (typep user 'cleavir-ir:funcall-instruction)
       (eq (first (cleavir-ir:inputs user)) fun)
       (not (member fun (rest (cleavir-ir:inputs user))))))

;;; Check if the given catch instruction has a continuation that is
;;; always unwound to from the stack frames of local or known
;;; functions.
(defun analyze-catch (catch function-dag ownership)
  (let ((continuation (first (cleavir-ir:outputs catch)))
        (catch-owner (gethash catch ownership)))
    ;; First copy propagate stuff, since we are checking if functions
    ;; escape.
    (cleavir-partial-inlining::copy-propagate-1 continuation)
    (let ((cont-uses (cleavir-ir:using-instructions continuation)))
      (dolist (cont-use cont-uses)
        (let ((unwind-owner (gethash cont-use ownership)))
          (unless (eq unwind-owner catch-owner)
            (analyze-unwind catch catch-owner function-dag unwind-owner ownership)))))))

;;; Check that none of the functions in the transitive closure of
;;; intermediate functions under the ``calls'' relation
;;; escape. Basically, these are the stack frames that can possibly be
;;; unwound from by a lexical non-local exit.
(defun analyze-unwind (catch catch-owner function-dag unwind-owner ownership)
  (let* ((worklist (cons unwind-owner
                         (cleavir-hir-transformations::add-intermediate-functions
                          (list unwind-owner)
                          function-dag
                          catch-owner)))
         (seen (copy-list worklist)))
    (loop (unless worklist
            (return))
          (let ((intermediate (pop worklist)))
            (dolist (node (gethash intermediate (cleavir-hir-transformations:dag-nodes function-dag)))
              (unless (typep node 'cleavir-hir-transformations::function-dag)
                (let ((fun (first (cleavir-ir:outputs (cleavir-hir-transformations:enclose-instruction node)))))
                  ;; Check that every call to a [unwind -> catch]
                  ;; intermediate local function is in call
                  ;; position.
                  (block escaped
                    (dolist (user (cleavir-ir:using-instructions fun))
                      (unless (call-position-p fun user)
                        (change-class catch 'escape-catch-instruction)
                        (return-from escaped))
                      ;; Also check that the function contains no
                      ;; unwind-protect or dynamic binding, since
                      ;; Clasp uses C++ exceptions to handle tese.
                      ;; FIXME: This is more coarse than it needs to
                      ;; be. Really, something more sophisticated can
                      ;; be done by more precisely checking the dynenv
                      ;; chain. But that can get messy
                      ;; fast. Definitely change over to using dynenvs
                      ;; if the coarseness turns out to be a big
                      ;; problem.
                      (when (cleavir-ir:local-instructions-of-type intermediate '(or clasp-cleavir-hir:unwind-protect-instruction clasp-cleavir-hir:bind-instruction))
                        (change-class catch 'escape-catch-instruction)
                        (return-from escaped))
                      ;; This logic iteratively computes the
                      ;; transitive closure we desire back
                      ;; into the worklist.
                      (let ((user-owner (gethash user ownership)))
                        (unless (eq user-owner catch-owner)
                          (dolist (user-intermediate (intermediate-functions unwind-owner function-dag catch-owner))
                            (unless (member user-owner seen)
                              (push user-owner seen)
                              (pushnew user-owner worklist))
                            (unless (member user-intermediate seen)
                              (push user-intermediate seen)
                              (pushnew user-intermediate worklist))))))))))))))
