package com.example.backend.presentation.controllers;

import java.util.List;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.security.core.annotation.AuthenticationPrincipal;
import org.springframework.security.core.userdetails.UserDetails;
import com.example.backend.presentation.entities.response.ErrorResponse;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import com.example.backend.business.entities.AssignmentDTO;
import com.example.backend.business.entities.CreateAssignmentDTO;
import com.example.backend.business.entities.EvaluateSubmissionDTO;
import com.example.backend.business.entities.SubmitAssignmentDTO;
import com.example.backend.business.service.interfaces.IAssignmentService;
import com.example.backend.core.exceptions.NotFoundException;
import com.example.backend.presentation.entities.request.EvaluateSubmissionRequest;
import com.example.backend.presentation.entities.request.SubmitAssignmentRequest;
import com.example.backend.presentation.entities.response.BaseResponse;

@RestController
@RequestMapping("/assignments")
public class AssignmentController {

    @Autowired
    private IAssignmentService assignmentService;

    @PostMapping
    public ResponseEntity<BaseResponse<Long>> createAssignment(@RequestBody CreateAssignmentDTO createAssignmentDTO,
            @AuthenticationPrincipal UserDetails userDetails) {
        try {
            var userId = Long.parseLong(userDetails.getUsername());
            Long assignmentId = assignmentService.createAssignment(userId, createAssignmentDTO);
            var response = new BaseResponse<Long>(assignmentId, 201);
            return ResponseEntity.status(201).body(response);
        } catch (NotFoundException e) {
            var response = new ErrorResponse<Long, CreateAssignmentDTO>(createAssignmentDTO, e.getMessage(), 404);
            return ResponseEntity.status(404).body(response);
        } catch (Exception e) {
            var response = new ErrorResponse<Long, CreateAssignmentDTO>(createAssignmentDTO, "Internal server error",
                    500);
            return ResponseEntity.status(500).body(response);
        }
    }

    @GetMapping("/stud/all")
    public ResponseEntity<BaseResponse<List<AssignmentDTO>>> getStudentsAssignments(
            @AuthenticationPrincipal UserDetails user) {
        try {
            Long userId = Long.parseLong(user.getUsername());
            List<AssignmentDTO> assignments = assignmentService.getStudentAssignments(userId);
            var response = new BaseResponse<List<AssignmentDTO>>(assignments, 200);
            return ResponseEntity.ok(response);
        } catch (NotFoundException e) {
            var response = new ErrorResponse<List<AssignmentDTO>, String>(null, e.getMessage(), 404);
            return ResponseEntity.status(404).body(response);
        } catch (Exception e) {
            var response = new ErrorResponse<List<AssignmentDTO>, String>(null, "Internal server error", 500);
            return ResponseEntity.status(500).body(response);
        }
    }

    @GetMapping("/teacher/all")
    public ResponseEntity<BaseResponse<List<AssignmentDTO>>> getTeachersAssignments(
            @AuthenticationPrincipal UserDetails user) {
        try {
            Long userId = Long.parseLong(user.getUsername());
            List<AssignmentDTO> assignments = assignmentService.getTeacherAssignments(userId);
            var response = new BaseResponse<List<AssignmentDTO>>(assignments, 200);
            return ResponseEntity.ok(response);
        } catch (NotFoundException e) {
            var response = new ErrorResponse<List<AssignmentDTO>, String>(null, e.getMessage(), 404);
            return ResponseEntity.status(404).body(response);
        } catch (Exception e) {
            var response = new ErrorResponse<List<AssignmentDTO>, String>(null, "Internal server error", 500);
            return ResponseEntity.status(500).body(response);
        }
    }

    @PostMapping("/grade/submissionId")
    public ResponseEntity<BaseResponse<Void>> gradeAssignment(
            @AuthenticationPrincipal UserDetails user,
            @PathVariable Long submissionId,
            @RequestBody EvaluateSubmissionRequest evaluateSubmissionRequest) {
        try {
            Long teacherId = Long.parseLong(user.getUsername());
            var evaluateSubmissionDTO = new EvaluateSubmissionDTO(
                    submissionId,
                    teacherId,
                    evaluateSubmissionRequest.getGrade(),
                    evaluateSubmissionRequest.getFeedback());
            assignmentService.gradeAssignment(evaluateSubmissionDTO);
            var response = new BaseResponse<Void>(null, HttpStatus.OK.value());
            return ResponseEntity.status(HttpStatus.OK).body(response);
        } catch (NotFoundException e) {
            var response = new ErrorResponse<Void, EvaluateSubmissionRequest>(
                    evaluateSubmissionRequest, e.getMessage(), HttpStatus.NOT_FOUND.value());
            return ResponseEntity.status(HttpStatus.NOT_FOUND).body(response);
        } catch (Exception e) {
            var response = new ErrorResponse<Void, EvaluateSubmissionRequest>(
                    evaluateSubmissionRequest, "Internal server error", HttpStatus.INTERNAL_SERVER_ERROR.value());
            return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR.value()).body(response);
        }
    }

    @PostMapping("/submit/{assignmentId}")
    public ResponseEntity<BaseResponse<Void>> submitAssignment(
            @AuthenticationPrincipal UserDetails user,
            @PathVariable Long assignmentId,
            @RequestBody SubmitAssignmentRequest submitAssignmentRequest) {
        try {
            Long studentId = Long.parseLong(user.getUsername());
            var submitAssignmentDTO = new SubmitAssignmentDTO(
                    assignmentId,
                    studentId,
                    submitAssignmentRequest.getContent());
            assignmentService.submitAssignment(submitAssignmentDTO);
            var response = new BaseResponse<Void>(null, HttpStatus.OK.value());
            return ResponseEntity.status(HttpStatus.OK).body(response);
        } catch (NotFoundException e) {
            var response = new ErrorResponse<Void, SubmitAssignmentDTO>(
                    null, e.getMessage(), HttpStatus.NOT_FOUND.value());
            return ResponseEntity.status(HttpStatus.NOT_FOUND).body(response);
        } catch (Exception e) {
            var response = new ErrorResponse<Void, SubmitAssignmentDTO>(
                    null, "Internal server error", HttpStatus.INTERNAL_SERVER_ERROR.value());
            return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR.value()).body(response);
        }
    }
}
