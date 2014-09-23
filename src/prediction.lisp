;;; Copyright (c) 2013, Jan Winkler <winkler@cs.uni-bremen.de>
;;; All rights reserved.
;;; 
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions are met:
;;; 
;;;     * Redistributions of source code must retain the above copyright
;;;       notice, this list of conditions and the following disclaimer.
;;;     * Redistributions in binary form must reproduce the above copyright
;;;       notice, this list of conditions and the following disclaimer in the
;;;       documentation and/or other materials provided with the distribution.
;;;     * Neither the name of the Universitaet Bremen nor the names of its contributors 
;;;       may be used to endorse or promote products derived from this software 
;;;       without specific prior written permission.
;;; 
;;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;;; AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
;;; LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;;; CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;;; SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;;; CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;;; ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;;; POSSIBILITY OF SUCH DAMAGE.

(in-package :cram-prediction)

(defvar *enable-prediction* nil)

(define-hook cram-language::on-invert-decision-tree (target-result features))
(define-hook cram-language::on-annotate-parameters (parameters))
(define-hook cram-language::on-predict (active-parameters requested-features))
(define-hook cram-language::on-load-model (file))
(define-hook cram-language::on-load-decision-tree (file))

(defun load-model (file)
  (cram-language::on-load-model file))

(defun load-decision-tree (file)
  (cram-language::on-load-decision-tree file))

(defun annotate-parameters (parameters)
  (format t "Annotate parameters: ~a~%" parameters)
  (first (cram-language::on-annotate-parameters parameters)))

(defun annotate-parameter (symbol value)
  (annotate-parameters `((,symbol ,value))))

(defun predict (active-parameters requested-features)
  "Predict the outcome of the current branch."
  (cram-language::on-predict active-parameters requested-features))

(defgeneric call-predict (active-features requested-features))

(defmethod call-predict ((active-features hash-table)
                         (requested-features hash-table))
  (call-predict (hash-table->list active-features)
                (hash-table->list requested-features)))

(defmethod call-predict ((active-features list)
                         (requested-features hash-table))
  (call-predict active-features (hash-table->list requested-features)))

(defmethod call-predict ((active-features hash-table)
                         (requested-features list))
  (call-predict (hash-table->list active-features) requested-features))

(defmethod call-predict ((active-features list) (requested-features list))
  (let ((prediction-result (first (predict active-features requested-features))))
    (gethash 'desig-props::failures prediction-result)))

(defun predict-failures (features-hash-table)
  (format t "Predicting all possible failures~%")
  (predict features-hash-table `(failures)))

(defun predict-values-hash-table (keys features-hash-table)
  (format t "Predicting values with keys: ~a~%" keys)
  (predict features-hash-table keys))

(defun annotate-features (features-hash-table)
  (loop for h being the hash-keys of features-hash-table
        as v = (gethash h features-hash-table)
        do (annotate-parameter h v)))

(defun hash-table->list (hash-table)
  (loop for k being the hash-keys of hash-table
        collect `(,k ,(gethash k hash-table))))

(defmacro cut:choose (tag
                      &key generators features
                       constraints (attempts 1) predicting
                       (predicting-attempts (1- attempts))
                       body)
  (let ((parameters (alexandria:flatten
                     (mapcar (lambda (generator)
                               (destructuring-bind (vars gens)
                                   generator
                                 (declare (ignore gens))
                                 vars))
                             generators))))
    `(:tag ,tag
       (block choose-block
         (sleep 0.1)
         (let ((generated-param-hash-table (make-hash-table))
               (attempts ,attempts)
               (predicting-attempts ,predicting-attempts))
           (declare (ignorable generated-param-hash-table))
           (labels ((generate-parameters ()
                      ,@(loop for (variables generator) in generators
                              collect
                              `(let ((generated-values ,generator))
                                 ,@(loop for i from 0 below (length variables)
                                         as variable = (nth i variables)
                                         collect `(setf (gethash
                                                         ',variable
                                                         generated-param-hash-table)
                                                        (nth ,i generated-values)))))))
             (loop with continue = t
                   while (and continue (>= (decf attempts) 0))
                   do (progn
                        (generate-parameters)
                        (let* ,(mapcar (lambda (parameter)
                                         `(,parameter (gethash
                                                       ',parameter
                                                       generated-param-hash-table)))
                                parameters)
                          ,@(mapcar (lambda (parameter)
                                      `(declare (ignorable ,parameter)))
                                    parameters)
                          (let* ,(append
                                  `((feature-hashes (make-hash-table)))
                                  (mapcar (lambda (feature)
                                            (destructuring-bind (var gen)
                                                feature
                                              `(,var (setf (gethash
                                                            ',var feature-hashes)
                                                           ,gen))))
                                          features))
                            ,@(mapcar (lambda (feature)
                                        (destructuring-bind (var gen) feature
                                          (declare (ignore gen))
                                          `(declare (ignorable ,var))))
                                      features)
                            (let ((predicted-failures
                                    (cond (cram-prediction::*enable-prediction*
                                           (cram-prediction::call-predict
                                            feature-hashes `(failures)))
                                          (t (make-hash-table)))))
                              (when (or (not cram-prediction::*enable-prediction*)
                                        (not (>= 0 (decf predicting-attempts)))
                                        (and ,@(mapcar
                                                (lambda (constraint)
                                                  (destructuring-bind (failure
                                                                       comparator)
                                                      constraint
                                                    `(let ((cut::predicted-failure
                                                             (gethash
                                                              ',failure
                                                              predicted-failures)))
                                                       (or (not cut::predicted-failure)
                                                           ,comparator))))
                                                constraints))
                                        (format t " -  Retry!~%"))
                                (setf continue nil)
                                (cram-prediction::annotate-features feature-hashes)
                                (let ((predicted-values
                                        (cond (cram-prediction::*enable-prediction*
                                               (cram-prediction::call-predict
                                                feature-hashes ',predicting))
                                              (t (make-hash-table)))))
                                  (labels ((predicted (key)
                                             (gethash key predicted-values)))
                                    (declare (ignorable (function predicted)))
                                    (return-from choose-block
                                      (values (progn ,body) t))))))))))
             (return-from choose-block (values nil nil))))))))
