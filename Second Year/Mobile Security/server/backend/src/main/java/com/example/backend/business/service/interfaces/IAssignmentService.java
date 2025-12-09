package com.example.backend.business.service.interfaces;

import java.util.List;

import com.example.backend.business.entities.AssignmentDTO;
import com.example.backend.business.entities.CreateAssignmentDTO;
import com.example.backend.business.entities.EvaluateSubmissionDTO;
import com.example.backend.business.entities.SubmitAssignmentDTO;
import com.example.backend.business.entities.UpdateAssignmentDTO;
import com.example.backend.core.exceptions.NotFoundException;

public interface IAssignmentService {
    Long createAssignment(Long teacherId, CreateAssignmentDTO createAssignmentDTO) throws NotFoundException;

    void deleteAssignment(Long assignmentId) throws NotFoundException;

    void updateAssignment(Long assignmentId, UpdateAssignmentDTO updateAssignmentDTO) throws NotFoundException;

    AssignmentDTO getAssignmentById(Long assignmentId) throws NotFoundException;

    List<AssignmentDTO> getStudentAssignments(Long studentId) throws NotFoundException;

    List<AssignmentDTO> getTeacherAssignments(Long teacherId) throws NotFoundException;

    void gradeAssignment(EvaluateSubmissionDTO evaluateSubmissionDTO)
            throws NotFoundException;

    void submitAssignment(SubmitAssignmentDTO submitAssignmentDTO) throws NotFoundException;
}
