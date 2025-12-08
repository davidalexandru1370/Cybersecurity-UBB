package com.example.backend.presentation.controllers;

import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import com.example.backend.presentation.entities.response.StatusResponse;

@RestController
@RequestMapping("/status")
public class StatusController {

    @GetMapping
    public ResponseEntity<StatusResponse> getStatus() {
        return ResponseEntity.ok(
                new StatusResponse("OK", new java.util.Date(), "1.0.0"));
    }
}
