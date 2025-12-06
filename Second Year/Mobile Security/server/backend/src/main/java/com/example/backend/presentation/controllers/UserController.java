package com.example.backend.presentation.controllers;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import com.example.backend.presentation.entities.request.CreateUserRequest;
import com.example.backend.presentation.entities.response.BaseResponse;

@RestController()
@RequestMapping("/user")
public class UserController {

    @GetMapping("/status")
    public String status() {
        return "User service is running.";
    }

    @PostMapping("/login")
    public BaseResponse<String> login(CreateUserRequest request) {
        return new BaseResponse<>("Login successful for user: " + request.getUsername(), 200);
    }
}
