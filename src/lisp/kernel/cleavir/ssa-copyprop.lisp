(in-package #:clasp-cleavir)

(defgeneric maybe-merge-data (instruction))

(defmethod maybe-merge-data (instruction)
  (declare (ignore instruction))
  nil)

(defmethod maybe-merge-data ((instruction cleavir-ir:assignment-instruction))
  (let ((input (first (cleavir-ir:inputs instruction)))
        (output (first (cleavir-ir:outputs instruction))))
    (when (and (typep input 'cleavir-ir:lexical-location)
               (typep output 'cleavir-ir:lexical-location))
      ;; Replace with a nop instruction to preserve flow graph structure
      (change-class instruction 'cleavir-ir:nop-instruction
                    :inputs '()
                    :outputs '())
      (dolist (output-use (cleavir-ir:using-instructions output))
        (nsubstitute input
                     output
                     (cleavir-ir:inputs output-use))))))

(defun ssa-copy-propagation (initial-instruction)
  (cleavir-ir:map-instructions-arbitrary-order #'maybe-merge-data initial-instruction)
  (cleavir-ir:reinitialize-data initial-instruction))
