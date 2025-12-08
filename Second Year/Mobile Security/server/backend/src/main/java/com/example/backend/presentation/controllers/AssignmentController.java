package com.example.backend.presentation.controllers;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.ResponseEntity;
import org.springframework.security.core.annotation.AuthenticationPrincipal;
import org.springframework.security.core.userdetails.UserDetails;
import com.example.backend.presentation.entities.response.ErrorResponse;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import com.example.backend.business.entities.CreateAssignmentDTO;
import com.example.backend.business.service.interfaces.IAssignmentService;
import com.example.backend.core.exceptions.NotFoundException;
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
}
